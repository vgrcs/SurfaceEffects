From Stdlib Require Import List.
From Stdlib Require Import Ascii.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Program.Equality.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.HeapFacts.
Require Import theories.NewSmallStep.Runtime.HeapNeutral.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.StateShape.
Require Import theories.NewSmallStep.Runtime.Typing.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Regularity.
Require Import theories.NewSmallStep.Typing.Resolve.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.

Inductive NRegularResolvedValShape : Heap -> NVal -> NTy -> Prop :=
| NRRVS_Nat :
    forall heap n,
      NRegularResolvedValShape heap (VNat n) TyNat
| NRRVS_Bool :
    forall heap b,
      NRegularResolvedValShape heap (VBool b) TyBool
| NRRVS_Unit :
    forall heap,
      NRegularResolvedValShape heap VUnit TyUnit
| NRRVS_Summary :
    forall heap theta,
      NRegularResolvedValShape heap (VSummary theta) TyEffect
| NRRVS_Pair :
    forall heap v1 v2 ty1 ty2,
      NRegularResolvedValShape heap v1 ty1 ->
      NRegularResolvedValShape heap v2 ty2 ->
      NRegularResolvedValShape heap (VPair v1 v2) (TyPair ty1 ty2)
| NRRVS_Loc :
    forall heap r l cell ty,
      heap_lookup r l heap = Some cell ->
      NRegularResolvedValShape heap cell ty ->
      NRegularResolvedValShape heap
        (VLoc r l)
        (TyRef (region_const_type r) ty)
| NRRVS_Closure :
    forall heap closure_env closure_rho f x ec ee
      gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      NRegularResolvedEnvShape closure_rho heap closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveTy closure_rho ty_arg ty_arg_res ->
      NResolveStaticEffect closure_rho eff_body eff_body_res ->
      NResolveTy closure_rho ty_body ty_body_res ->
      NResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NCheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      NRegularResolvedValShape heap
        (VClosure closure_env closure_rho f x ec ee)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
| NRRVS_RegionClosure :
    forall heap closure_env closure_rho x e gamma omega ty ty_res eff eff_res,
      NRegularResolvedEnvShape closure_rho heap closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveStaticEffect closure_rho (close_static_effect x eff) eff_res ->
      NResolveTy closure_rho (close_ty x ty) ty_res ->
      NCheckedRegionBody x gamma omega e ty eff ->
      NRegularResolvedValShape heap
        (VRegionClosure closure_env closure_rho x e)
        (TyForallRgn eff_res ty_res)
with NRegularResolvedEnvShape : Rho -> Heap -> NEnv -> NCtx -> Prop :=
| NRRES_EnvNil :
    forall rho heap,
      NRegularResolvedEnvShape rho heap EnvNil []
| NRRES_EnvCons :
    forall rho heap x v env ty ty_res gamma,
      NResolveTy rho ty ty_res ->
      NRegularResolvedValShape heap v ty_res ->
      NRegularResolvedEnvShape rho heap env gamma ->
      NRegularResolvedEnvShape rho heap (EnvCons x v env) ((x, ty) :: gamma).

Scheme NRegularResolvedValShape_ind' :=
  Induction for NRegularResolvedValShape Sort Prop
with NRegularResolvedEnvShape_ind' :=
  Induction for NRegularResolvedEnvShape Sort Prop.

Combined Scheme NRegularResolvedValShape_NRegularResolvedEnvShape_ind
  from NRegularResolvedValShape_ind', NRegularResolvedEnvShape_ind'.

Lemma NRegularResolvedEnvShape_lookup :
  forall rho heap env gamma x ty ty_res,
    NRegularResolvedEnvShape rho heap env gamma ->
    ctx_binds x ty gamma ->
    NResolveTy rho ty ty_res ->
    exists v,
      env_lookup x env = Some v /\
      NRegularResolvedValShape heap v ty_res.
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
        HVStored : NRegularResolvedValShape heap v ?ty_stored |- _ =>
          pose proof
            (NResolveTy_deterministic
              rho ty ty_stored ty_goal HStored HGoal)
            as HResolvedEq;
          subst ty_goal;
          exists v; split; [reflexivity | exact HVStored]
      end.
    + apply IH; assumption.
Qed.

Lemma NRegularResolvedEnvShape_extend :
  forall rho heap env gamma x v ty ty_res,
    NResolveTy rho ty ty_res ->
    NRegularResolvedValShape heap v ty_res ->
    NRegularResolvedEnvShape rho heap env gamma ->
    NRegularResolvedEnvShape rho heap
      (env_extend x v env)
      ((x, ty) :: gamma).
Proof.
  intros rho heap env gamma x v ty ty_res HResolve HVal HEnv.
  eapply NRRES_EnvCons; eauto.
Qed.

Lemma NRegularResolvedEnvShape_extend_fresh :
  forall rho heap env gamma omega x r_val,
    ~ In x omega ->
    NCtxWF omega gamma ->
    NRegularResolvedEnvShape rho heap env gamma ->
    NRegularResolvedEnvShape (rho_extend x r_val rho) heap env gamma.
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

Definition NRegularResolvedHeapShape (heap : Heap) : Prop :=
  forall r l v,
    heap_lookup r l heap = Some v ->
    exists ty,
      NRegularResolvedValShape heap v ty.

Lemma NRegularResolvedHeapShape_lookup :
  forall heap r l v,
    NRegularResolvedHeapShape heap ->
    heap_lookup r l heap = Some v ->
    exists ty,
      NRegularResolvedValShape heap v ty.
Proof.
  intros heap r l v HHeap HLookup.
  exact (HHeap r l v HLookup).
Qed.

Inductive NRegularResolvedKontShape :
    Heap -> NKont -> NTy -> NTy -> Prop :=
| NRRKS_Done :
    forall heap ty,
      NRegularResolvedKontShape heap KDone ty ty
| NRRKS_MuAppFun :
    forall heap ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty_arg ty_arg_res ->
      NResolveStaticEffect rho eff_body eff_body_res ->
      NResolveTy rho ty_body ty_body_res ->
      NResolveStaticEffect rho eff_summary eff_summary_res ->
      NCheckedTcExp gamma omega ea ty_arg eff_arg ->
      NRegularResolvedKontShape heap k ty_body_res ty_out ->
      NRegularResolvedKontShape heap
        (KMuAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| NRRKS_MuAppArg :
    forall heap closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      NRegularResolvedEnvShape closure_rho heap closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveTy closure_rho ty_arg ty_arg_res ->
      NResolveStaticEffect closure_rho eff_body eff_body_res ->
      NResolveTy closure_rho ty_body ty_body_res ->
      NResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NCheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      NRegularResolvedKontShape heap k ty_body_res ty_out ->
      NRegularResolvedKontShape heap
        (KMuAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| NRRKS_EffAppFun :
    forall heap ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty_arg ty_arg_res ->
      NResolveStaticEffect rho eff_body eff_body_res ->
      NResolveTy rho ty_body ty_body_res ->
      NResolveStaticEffect rho eff_summary eff_summary_res ->
      NCheckedTcExp gamma omega ea ty_arg eff_arg ->
      NRegularResolvedKontShape heap k TyEffect ty_out ->
      NRegularResolvedKontShape heap
        (KEffAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| NRRKS_EffAppArg :
    forall heap closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      NRegularResolvedEnvShape closure_rho heap closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveTy closure_rho ty_arg ty_arg_res ->
      NResolveStaticEffect closure_rho eff_body eff_body_res ->
      NResolveTy closure_rho ty_body ty_body_res ->
      NResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NCheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      NRegularResolvedKontShape heap k TyEffect ty_out ->
      NRegularResolvedKontShape heap
        (KEffAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| NRRKS_PairParEff1 :
    forall heap ef1 ea1 ef2 ea2 env rho k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 eff_summary2 ty_out,
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty1 ty1_res ->
      NResolveTy rho ty2 ty2_res ->
      NCheckedTcExp gamma omega
        (EMuApp ef1 ea1) ty1 eff1 ->
      NCheckedTcExp gamma omega
        (EMuApp ef2 ea2) ty2 eff2 ->
      NCheckedTcExp gamma omega
        (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      NRegularResolvedKontShape heap k (TyPair ty1_res ty2_res) ty_out ->
      NRegularResolvedKontShape heap
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
        TyEffect
        ty_out
| NRRKS_PairParEff2 :
    forall heap ef1 ea1 ef2 ea2 env rho theta1 k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 ty_out,
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty1 ty1_res ->
      NResolveTy rho ty2 ty2_res ->
      NCheckedTcExp gamma omega
        (EMuApp ef1 ea1) ty1 eff1 ->
      NCheckedTcExp gamma omega
        (EMuApp ef2 ea2) ty2 eff2 ->
      NRegularResolvedKontShape heap k (TyPair ty1_res ty2_res) ty_out ->
      NRegularResolvedKontShape heap
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
        TyEffect
        ty_out
| NRRKS_RgnApp :
    forall heap r arg_rho r_val k eff ty ty_out,
      eval_region arg_rho r = Some r_val ->
      NRegularResolvedKontShape heap k
        (open_ty_type (region_const_type r_val) ty)
        ty_out ->
      NRegularResolvedKontShape heap
        (KRgnApp r arg_rho k)
        (TyForallRgn eff ty)
        ty_out
| NRRKS_Cond :
    forall heap et ef env rho k gamma omega ty ty_res eff_t eff_f ty_out,
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty ty_res ->
      NCheckedTcExp gamma omega et ty eff_t ->
      NCheckedTcExp gamma omega ef ty eff_f ->
      NRegularResolvedKontShape heap k ty_res ty_out ->
      NRegularResolvedKontShape heap
        (KCond et ef env rho k)
        TyBool
        ty_out
| NRRKS_Ref :
    forall heap r ty k ty_out,
      NRegularResolvedKontShape heap k
        (TyRef (region_const_type r) ty)
        ty_out ->
      NRegularResolvedKontShape heap (KRef r k) ty ty_out
| NRRKS_Deref :
    forall heap rgn r ty k ty_out,
      NRegularResolvedKontShape heap k ty ty_out ->
      NRegularResolvedKontShape heap (KDeref rgn k)
        (TyRef (region_const_type r) ty) ty_out
| NRRKS_AssignLoc :
    forall heap rgn ev env rho k gamma omega r ty ty_res eff_v ty_out,
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      eval_region rho rgn = Some r ->
      NResolveTy rho ty ty_res ->
      NCheckedTcExp gamma omega ev ty eff_v ->
      NRegularResolvedKontShape heap k TyUnit ty_out ->
      NRegularResolvedKontShape heap
        (KAssignLoc rgn ev env rho k)
        (TyRef (region_const_type r) ty_res)
        ty_out
| NRRKS_AssignVal :
    forall heap rgn r ty loc k ty_out,
      NRegularResolvedValShape heap loc
        (TyRef (region_const_type r) ty) ->
      NRegularResolvedKontShape heap k TyUnit ty_out ->
      NRegularResolvedKontShape heap
        (KAssignVal rgn loc k)
        ty
        ty_out
| NRRKS_PlusL :
    forall heap e2 env rho k gamma omega eff ty_out,
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NRegularResolvedKontShape heap k TyNat ty_out ->
      NRegularResolvedKontShape heap
        (KPlusL e2 env rho k)
        TyNat
        ty_out
| NRRKS_PlusR :
    forall heap n k ty_out,
      NRegularResolvedKontShape heap k TyNat ty_out ->
      NRegularResolvedKontShape heap (KPlusR n k) TyNat ty_out
| NRRKS_MinusL :
    forall heap e2 env rho k gamma omega eff ty_out,
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NRegularResolvedKontShape heap k TyNat ty_out ->
      NRegularResolvedKontShape heap
        (KMinusL e2 env rho k)
        TyNat
        ty_out
| NRRKS_MinusR :
    forall heap n k ty_out,
      NRegularResolvedKontShape heap k TyNat ty_out ->
      NRegularResolvedKontShape heap (KMinusR n k) TyNat ty_out
| NRRKS_TimesL :
    forall heap e2 env rho k gamma omega eff ty_out,
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NRegularResolvedKontShape heap k TyNat ty_out ->
      NRegularResolvedKontShape heap
        (KTimesL e2 env rho k)
        TyNat
        ty_out
| NRRKS_TimesR :
    forall heap n k ty_out,
      NRegularResolvedKontShape heap k TyNat ty_out ->
      NRegularResolvedKontShape heap (KTimesR n k) TyNat ty_out
| NRRKS_EqL :
    forall heap e2 env rho k gamma omega eff ty_out,
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NRegularResolvedKontShape heap k TyBool ty_out ->
      NRegularResolvedKontShape heap
        (KEqL e2 env rho k)
        TyNat
        ty_out
| NRRKS_EqR :
    forall heap n k ty_out,
      NRegularResolvedKontShape heap k TyBool ty_out ->
      NRegularResolvedKontShape heap (KEqR n k) TyNat ty_out
| NRRKS_ReadConc :
    forall heap k r ty ty_out,
      NRegularResolvedKontShape heap k TyEffect ty_out ->
      NRegularResolvedKontShape heap
        (KReadConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| NRRKS_WriteConc :
    forall heap k r ty ty_out,
      NRegularResolvedKontShape heap k TyEffect ty_out ->
      NRegularResolvedKontShape heap
        (KWriteConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| NRRKS_ConcatL :
    forall heap e2 env rho k gamma omega eff ty_out,
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyEffect eff ->
      NRegularResolvedKontShape heap k TyEffect ty_out ->
      NRegularResolvedKontShape heap
        (KConcatL e2 env rho k)
        TyEffect
        ty_out
| NRRKS_ConcatR :
    forall heap theta k ty_out,
      NRegularResolvedKontShape heap k TyEffect ty_out ->
      NRegularResolvedKontShape heap
        (KConcatR theta k)
        TyEffect
        ty_out.

Inductive NRegularResolvedStateShape : NState -> NTy -> Prop :=
| NRRSS_Eval :
    forall heap env rho e k gamma omega ty ty_res eff ty_out,
      NRegularResolvedHeapShape heap ->
      NRegularResolvedEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty ty_res ->
      NCheckedTcExp gamma omega e ty eff ->
      NRegularResolvedKontShape heap k ty_res ty_out ->
      NRegularResolvedStateShape (StEval heap env rho e k) ty_out
| NRRSS_Return :
    forall heap v k ty ty_out,
      NRegularResolvedHeapShape heap ->
      NRegularResolvedValShape heap v ty ->
      NRegularResolvedKontShape heap k ty ty_out ->
      NRegularResolvedStateShape (StReturn heap v k) ty_out
| NRRSS_Done :
    forall heap v ty,
      NRegularResolvedHeapShape heap ->
      NRegularResolvedValShape heap v ty ->
      NRegularResolvedStateShape (StDone heap v) ty
| NRRSS_Error :
    forall heap ty,
      NRegularResolvedHeapShape heap ->
      NRegularResolvedStateShape (StError heap) ty
| NRRSS_PairParRun :
    forall left_state right_state phi_left phi_right k
      heap ty1 ty2 ty_out,
      state_heap left_state = heap ->
      state_heap right_state = heap ->
      NRegularResolvedStateShape left_state ty1 ->
      NRegularResolvedStateShape right_state ty2 ->
      NRegularResolvedKontShape heap k (TyPair ty1 ty2) ty_out ->
      NRegularResolvedStateShape
        (StPairParRun left_state right_state phi_left phi_right k)
        ty_out.

Lemma NRegularResolvedValShape_to_resolved :
  forall heap v ty,
    NRegularResolvedValShape heap v ty ->
    NResolvedValShape heap v ty
with NRegularResolvedEnvShape_to_resolved :
  forall rho heap env gamma,
    NRegularResolvedEnvShape rho heap env gamma ->
    NResolvedEnvShape rho heap env gamma.
Proof.
  - intros heap v ty HVal.
    induction HVal.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + eapply NRVS_Pair; eauto.
    + eapply NRVS_Loc; eauto.
    + eapply NRVS_Closure; eauto using NCheckedTcExp_to_NTcExp.
    + eapply NRVS_RegionClosure; eauto.
      eapply NCheckedRegionBody_to_NTcExp; eauto.
  - intros rho heap env gamma HEnv.
    induction HEnv.
    + constructor.
    + econstructor; eauto.
Qed.

Lemma NRegularResolvedHeapShape_to_resolved :
  forall heap,
    NRegularResolvedHeapShape heap ->
    NResolvedHeapShape heap.
Proof.
  unfold NRegularResolvedHeapShape, NResolvedHeapShape.
  intros heap HHeap r l v HLookup.
  destruct (HHeap r l v HLookup) as (ty & HVal).
  exists ty.
  eapply NRegularResolvedValShape_to_resolved; eauto.
Qed.

Lemma NRegularResolvedKontShape_to_resolved :
  forall heap k ty_in ty_out,
    NRegularResolvedKontShape heap k ty_in ty_out ->
    NResolvedKontShape heap k ty_in ty_out.
Proof.
  intros heap k ty_in ty_out HK.
  induction HK.
  - constructor.
  - eapply NRKS_MuAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_MuAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_EffAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_EffAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_PairParEff1 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2)
      (eff_summary2 := eff_summary2);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_PairParEff2 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_RgnApp; eauto.
  - eapply NRKS_Cond with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_t := eff_t) (eff_f := eff_f);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_Ref; eauto.
  - eapply NRKS_Deref; eauto.
  - eapply NRKS_AssignLoc with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_v := eff_v);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_AssignVal; eauto using
      NRegularResolvedValShape_to_resolved.
  - eapply NRKS_PlusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_PlusR; eauto.
  - eapply NRKS_MinusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_MinusR; eauto.
  - eapply NRKS_TimesL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_TimesR; eauto.
  - eapply NRKS_EqL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_EqR; eauto.
  - eapply NRKS_ReadConc; eauto.
  - eapply NRKS_WriteConc; eauto.
  - eapply NRKS_ConcatL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using
        NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp.
  - eapply NRKS_ConcatR; eauto.
Qed.

Lemma NRegularResolvedStateShape_to_resolved :
  forall state ty,
    NRegularResolvedStateShape state ty ->
    NResolvedStateShape state ty.
Proof.
  intros state ty HState.
  induction HState.
  - eapply NRSS_Eval; eauto using
      NRegularResolvedHeapShape_to_resolved,
      NRegularResolvedEnvShape_to_resolved,
        NCheckedTcExp_to_NTcExp,
      NRegularResolvedKontShape_to_resolved.
  - eapply NRSS_Return; eauto using
      NRegularResolvedHeapShape_to_resolved,
      NRegularResolvedValShape_to_resolved,
      NRegularResolvedKontShape_to_resolved.
  - eapply NRSS_Done; eauto using
      NRegularResolvedHeapShape_to_resolved,
      NRegularResolvedValShape_to_resolved.
  - eapply NRSS_Error; eauto using
      NRegularResolvedHeapShape_to_resolved.
  - eapply NRSS_PairParRun; eauto using
      NRegularResolvedKontShape_to_resolved.
Qed.

Lemma NRegularResolvedStateShape_initial :
  forall heap env rho e gamma omega ty ty_res eff,
    NRegularResolvedHeapShape heap ->
    NRegularResolvedEnvShape rho heap env gamma ->
    NRhoModels omega rho ->
    NResolveTy rho ty ty_res ->
    NCheckedTcExp gamma omega e ty eff ->
    NRegularResolvedStateShape (NInitialState heap env rho e) ty_res.
Proof.
  intros heap env rho e gamma omega ty ty_res eff
    HHeap HEnv HRho HResolve HTyped.
  unfold NInitialState.
  eapply NRRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty) (eff := eff);
    eauto.
  constructor.
Qed.

Corollary NRegularResolvedStateShape_initial_effect :
  forall heap env rho e gamma omega eff,
    NRegularResolvedHeapShape heap ->
    NRegularResolvedEnvShape rho heap env gamma ->
    NRhoModels omega rho ->
    NCheckedTcExp gamma omega e TyEffect eff ->
    NRegularResolvedStateShape (NInitialState heap env rho e) TyEffect.
Proof.
  intros heap env rho e gamma omega eff HHeap HEnv HRho HTyped.
  eapply NRegularResolvedStateShape_initial; eauto using NResolve_Effect.
Qed.

Lemma NCheckedResolvedStateShape_initial :
  forall heap env rho e gamma omega ty ty_res eff,
    NRegularResolvedHeapShape heap ->
    NRegularResolvedEnvShape rho heap env gamma ->
    NRhoModels omega rho ->
    NResolveTy rho ty ty_res ->
    NCheckedTcExp gamma omega e ty eff ->
    NRegularResolvedStateShape (NInitialState heap env rho e) ty_res.
Proof.
  intros heap env rho e gamma omega ty ty_res eff
    HHeap HEnv HRho HResolve HChecked.
  eapply NRegularResolvedStateShape_initial; eauto.
Qed.

Corollary NCheckedResolvedStateShape_initial_effect :
  forall heap env rho e gamma omega eff,
    NRegularResolvedHeapShape heap ->
    NRegularResolvedEnvShape rho heap env gamma ->
    NRhoModels omega rho ->
    NCheckedTcExp gamma omega e TyEffect eff ->
    NRegularResolvedStateShape (NInitialState heap env rho e) TyEffect.
Proof.
  intros heap env rho e gamma omega eff HHeap HEnv HRho HChecked.
  eapply NCheckedResolvedStateShape_initial; eauto using NResolve_Effect.
Qed.

Lemma NRegularResolvedStateShape_aligned :
  forall state ty,
    NRegularResolvedStateShape state ty ->
    NStateHeapsAligned state.
Proof.
  intros state ty HState.
  induction HState; simpl; try exact I.
  repeat split; assumption || congruence.
Qed.

Definition NStoreTyping := list (RegionId * Location * NTy).

Fixpoint store_ty_lookup
    (r : RegionId) (l : Location)
    (store : NStoreTyping) : option NTy :=
  match store with
  | [] => None
  | (r', l', ty) :: store' =>
      if Nat.eqb r r' && Nat.eqb l l'
      then Some ty
      else store_ty_lookup r l store'
  end.

Definition NStoreKeysBoundedByHeap
    (heap : Heap) (store : NStoreTyping) : Prop :=
  forall r l ty,
    In (r, l, ty) store ->
    l < length heap.

Lemma store_ty_lookup_deterministic :
  forall store r l ty1 ty2,
    store_ty_lookup r l store = Some ty1 ->
    store_ty_lookup r l store = Some ty2 ->
    ty1 = ty2.
Proof.
  intros store r l ty1 ty2 HLookup1 HLookup2.
  rewrite HLookup1 in HLookup2.
  inversion HLookup2; reflexivity.
Qed.

Lemma store_ty_lookup_in :
  forall store r l ty,
    store_ty_lookup r l store = Some ty ->
    In (r, l, ty) store.
Proof.
  induction store as [| [[r0 l0] ty0] store IH];
    intros r l ty HLookup; simpl in *.
  - inversion HLookup.
  - destruct (Nat.eqb r r0 && Nat.eqb l l0) eqn:HEq.
    + apply andb_true_iff in HEq.
      destruct HEq as [HR HL].
      apply Nat.eqb_eq in HR.
      apply Nat.eqb_eq in HL.
      inversion HLookup; subst.
      left. subst. reflexivity.
    + right. eapply IH; eauto.
Qed.

Lemma store_ty_lookup_extend_same :
  forall store r l ty,
    store_ty_lookup r l ((r, l, ty) :: store) = Some ty.
Proof.
  intros store r l ty.
  simpl.
  rewrite Nat.eqb_refl, Nat.eqb_refl.
  reflexivity.
Qed.

Lemma store_ty_lookup_extend_old :
  forall heap store r_new l_new ty_new r l ty,
    NStoreKeysBoundedByHeap heap store ->
    l_new = length heap ->
    store_ty_lookup r l store = Some ty ->
    store_ty_lookup r l ((r_new, l_new, ty_new) :: store) = Some ty.
Proof.
  intros heap store r_new l_new ty_new r l ty
    HBounded HFresh HLookup.
  simpl.
  destruct (Nat.eqb r r_new && Nat.eqb l l_new) eqn:HEq;
    [| exact HLookup].
  apply andb_true_iff in HEq.
  destruct HEq as [_ HL].
  apply Nat.eqb_eq in HL.
  subst l_new.
  subst l.
  pose proof (store_ty_lookup_in store r (length heap) ty HLookup)
    as HIn.
  pose proof (HBounded r (length heap) ty HIn) as HLen.
  lia.
Qed.

Inductive NStoreResolvedValShape : NStoreTyping -> NVal -> NTy -> Prop :=
| NSRVS_Nat :
    forall store n,
      NStoreResolvedValShape store (VNat n) TyNat
| NSRVS_Bool :
    forall store b,
      NStoreResolvedValShape store (VBool b) TyBool
| NSRVS_Unit :
    forall store,
      NStoreResolvedValShape store VUnit TyUnit
| NSRVS_Summary :
    forall store theta,
      NStoreResolvedValShape store (VSummary theta) TyEffect
| NSRVS_Pair :
    forall store v1 v2 ty1 ty2,
      NStoreResolvedValShape store v1 ty1 ->
      NStoreResolvedValShape store v2 ty2 ->
      NStoreResolvedValShape store (VPair v1 v2) (TyPair ty1 ty2)
| NSRVS_Loc :
    forall store r l ty,
      store_ty_lookup r l store = Some ty ->
      NStoreResolvedValShape store
        (VLoc r l)
        (TyRef (region_const_type r) ty)
| NSRVS_Closure :
    forall store closure_env closure_rho f x ec ee
      gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      NStoreResolvedEnvShape store closure_rho closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveTy closure_rho ty_arg ty_arg_res ->
      NResolveStaticEffect closure_rho eff_body eff_body_res ->
      NResolveTy closure_rho ty_body ty_body_res ->
      NResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NCheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      NStoreResolvedValShape store
        (VClosure closure_env closure_rho f x ec ee)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
| NSRVS_RegionClosure :
    forall store closure_env closure_rho x e gamma omega ty ty_res eff eff_res,
      NStoreResolvedEnvShape store closure_rho closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveStaticEffect closure_rho (close_static_effect x eff) eff_res ->
      NResolveTy closure_rho (close_ty x ty) ty_res ->
      NCheckedRegionBody x gamma omega e ty eff ->
      NStoreResolvedValShape store
        (VRegionClosure closure_env closure_rho x e)
        (TyForallRgn eff_res ty_res)
with NStoreResolvedEnvShape : NStoreTyping -> Rho -> NEnv -> NCtx -> Prop :=
| NSRES_EnvNil :
    forall store rho,
      NStoreResolvedEnvShape store rho EnvNil []
| NSRES_EnvCons :
    forall store rho x v env ty ty_res gamma,
      NResolveTy rho ty ty_res ->
      NStoreResolvedValShape store v ty_res ->
      NStoreResolvedEnvShape store rho env gamma ->
      NStoreResolvedEnvShape store rho (EnvCons x v env) ((x, ty) :: gamma).

Scheme NStoreResolvedValShape_ind' :=
  Induction for NStoreResolvedValShape Sort Prop
with NStoreResolvedEnvShape_ind' :=
  Induction for NStoreResolvedEnvShape Sort Prop.

Combined Scheme NStoreResolvedValShape_NStoreResolvedEnvShape_ind
  from NStoreResolvedValShape_ind', NStoreResolvedEnvShape_ind'.

Lemma NStoreResolvedEnvShape_lookup :
  forall store rho env gamma x ty ty_res,
    NStoreResolvedEnvShape store rho env gamma ->
    ctx_binds x ty gamma ->
    NResolveTy rho ty ty_res ->
    exists v,
      env_lookup x env = Some v /\
      NStoreResolvedValShape store v ty_res.
Proof.
  intros store rho env gamma x ty ty_res HEnv.
  induction HEnv as
    [store rho
    | store rho y v env ty_y ty_y_res gamma
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
        HVStored : NStoreResolvedValShape store v ?ty_stored |- _ =>
          pose proof
            (NResolveTy_deterministic
              rho ty ty_stored ty_goal HStored HGoal)
            as HResolvedEq;
          subst ty_goal;
          exists v; split; [reflexivity | exact HVStored]
      end.
    + apply IH; assumption.
Qed.

Lemma NStoreResolvedEnvShape_extend :
  forall store rho env gamma x v ty ty_res,
    NResolveTy rho ty ty_res ->
    NStoreResolvedValShape store v ty_res ->
    NStoreResolvedEnvShape store rho env gamma ->
    NStoreResolvedEnvShape store rho
      (env_extend x v env)
      ((x, ty) :: gamma).
Proof.
  intros store rho env gamma x v ty ty_res HResolve HVal HEnv.
  eapply NSRES_EnvCons; eauto.
Qed.

Lemma NStoreResolvedEnvShape_extend_fresh :
  forall store rho env gamma omega x r_val,
    ~ In x omega ->
    NCtxWF omega gamma ->
    NStoreResolvedEnvShape store rho env gamma ->
    NStoreResolvedEnvShape store (rho_extend x r_val rho) env gamma.
Proof.
  intros store rho env gamma omega x r_val HFresh HCtxWF HEnv.
  induction HEnv as
    [store rho
    | store rho y v env ty ty_res gamma HResolve HV HEnv IH].
  - constructor.
  - inversion HCtxWF as [| binding gamma_tail HBindingWF HCtxTailWF];
      subst; simpl in HBindingWF.
    econstructor; eauto.
    eapply NResolveTy_extend_fresh; eauto.
Qed.

Definition NStoreResolvedHeapShape
    (heap : Heap) (store : NStoreTyping) : Prop :=
  (forall r l v,
    heap_lookup r l heap = Some v ->
    exists ty,
      store_ty_lookup r l store = Some ty /\
      NStoreResolvedValShape store v ty) /\
  (forall r l ty,
    store_ty_lookup r l store = Some ty ->
    exists v,
      heap_lookup r l heap = Some v /\
      NStoreResolvedValShape store v ty).

Definition NStoreResolvedRuntimeShape
    (heap : Heap) (store : NStoreTyping)
    (env : NEnv) (rho : Rho) (gamma : NCtx) : Prop :=
  NStoreKeysBoundedByHeap heap store /\
  NStoreResolvedHeapShape heap store /\
  NStoreResolvedEnvShape store rho env gamma.

Inductive NStoreResolvedKontShape :
    NStoreTyping -> NKont -> NTy -> NTy -> Prop :=
| NSRKS_Done :
    forall store ty,
      NStoreResolvedKontShape store KDone ty ty
| NSRKS_MuAppFun :
    forall store ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty_arg ty_arg_res ->
      NResolveStaticEffect rho eff_body eff_body_res ->
      NResolveTy rho ty_body ty_body_res ->
      NResolveStaticEffect rho eff_summary eff_summary_res ->
      NCheckedTcExp gamma omega ea ty_arg eff_arg ->
      NStoreResolvedKontShape store k ty_body_res ty_out ->
      NStoreResolvedKontShape store
        (KMuAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| NSRKS_MuAppArg :
    forall store closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      NStoreResolvedEnvShape store closure_rho closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveTy closure_rho ty_arg ty_arg_res ->
      NResolveStaticEffect closure_rho eff_body eff_body_res ->
      NResolveTy closure_rho ty_body ty_body_res ->
      NResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NCheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      NStoreResolvedKontShape store k ty_body_res ty_out ->
      NStoreResolvedKontShape store
        (KMuAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| NSRKS_EffAppFun :
    forall store ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty_arg ty_arg_res ->
      NResolveStaticEffect rho eff_body eff_body_res ->
      NResolveTy rho ty_body ty_body_res ->
      NResolveStaticEffect rho eff_summary eff_summary_res ->
      NCheckedTcExp gamma omega ea ty_arg eff_arg ->
      NStoreResolvedKontShape store k TyEffect ty_out ->
      NStoreResolvedKontShape store
        (KEffAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| NSRKS_EffAppArg :
    forall store closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      NStoreResolvedEnvShape store closure_rho closure_env gamma ->
      NRhoModels omega closure_rho ->
      NResolveTy closure_rho ty_arg ty_arg_res ->
      NResolveStaticEffect closure_rho eff_body eff_body_res ->
      NResolveTy closure_rho ty_body ty_body_res ->
      NResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NCheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      NStoreResolvedKontShape store k TyEffect ty_out ->
      NStoreResolvedKontShape store
        (KEffAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| NSRKS_PairParEff1 :
    forall store ef1 ea1 ef2 ea2 env rho k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 eff_summary2 ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty1 ty1_res ->
      NResolveTy rho ty2 ty2_res ->
      NCheckedTcExp gamma omega
        (EMuApp ef1 ea1) ty1 eff1 ->
      NCheckedTcExp gamma omega
        (EMuApp ef2 ea2) ty2 eff2 ->
      NCheckedTcExp gamma omega
        (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      NStoreResolvedKontShape store k (TyPair ty1_res ty2_res) ty_out ->
      NStoreResolvedKontShape store
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
        TyEffect
        ty_out
| NSRKS_PairParEff2 :
    forall store ef1 ea1 ef2 ea2 env rho theta1 k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty1 ty1_res ->
      NResolveTy rho ty2 ty2_res ->
      NCheckedTcExp gamma omega
        (EMuApp ef1 ea1) ty1 eff1 ->
      NCheckedTcExp gamma omega
        (EMuApp ef2 ea2) ty2 eff2 ->
      NStoreResolvedKontShape store k (TyPair ty1_res ty2_res) ty_out ->
      NStoreResolvedKontShape store
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
        TyEffect
        ty_out
| NSRKS_RgnApp :
    forall store r arg_rho r_val k eff ty ty_out,
      eval_region arg_rho r = Some r_val ->
      NStoreResolvedKontShape store k
        (open_ty_type (region_const_type r_val) ty)
        ty_out ->
      NStoreResolvedKontShape store
        (KRgnApp r arg_rho k)
        (TyForallRgn eff ty)
        ty_out
| NSRKS_Cond :
    forall store et ef env rho k gamma omega ty ty_res eff_t eff_f ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty ty_res ->
      NCheckedTcExp gamma omega et ty eff_t ->
      NCheckedTcExp gamma omega ef ty eff_f ->
      NStoreResolvedKontShape store k ty_res ty_out ->
      NStoreResolvedKontShape store
        (KCond et ef env rho k)
        TyBool
        ty_out
| NSRKS_Ref :
    forall store r ty k ty_out,
      NStoreResolvedKontShape store k
        (TyRef (region_const_type r) ty)
        ty_out ->
      NStoreResolvedKontShape store (KRef r k) ty ty_out
| NSRKS_Deref :
    forall store rgn r ty k ty_out,
      NStoreResolvedKontShape store k ty ty_out ->
      NStoreResolvedKontShape store (KDeref rgn k)
        (TyRef (region_const_type r) ty) ty_out
| NSRKS_AssignLoc :
    forall store rgn ev env rho k gamma omega r ty ty_res eff_v ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      eval_region rho rgn = Some r ->
      NResolveTy rho ty ty_res ->
      NCheckedTcExp gamma omega ev ty eff_v ->
      NStoreResolvedKontShape store k TyUnit ty_out ->
      NStoreResolvedKontShape store
        (KAssignLoc rgn ev env rho k)
        (TyRef (region_const_type r) ty_res)
        ty_out
| NSRKS_AssignVal :
    forall store rgn r ty loc k ty_out,
      NStoreResolvedValShape store loc
        (TyRef (region_const_type r) ty) ->
      NStoreResolvedKontShape store k TyUnit ty_out ->
      NStoreResolvedKontShape store
        (KAssignVal rgn loc k)
        ty
        ty_out
| NSRKS_PlusL :
    forall store e2 env rho k gamma omega eff ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NStoreResolvedKontShape store k TyNat ty_out ->
      NStoreResolvedKontShape store
        (KPlusL e2 env rho k)
        TyNat
        ty_out
| NSRKS_PlusR :
    forall store n k ty_out,
      NStoreResolvedKontShape store k TyNat ty_out ->
      NStoreResolvedKontShape store (KPlusR n k) TyNat ty_out
| NSRKS_MinusL :
    forall store e2 env rho k gamma omega eff ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NStoreResolvedKontShape store k TyNat ty_out ->
      NStoreResolvedKontShape store
        (KMinusL e2 env rho k)
        TyNat
        ty_out
| NSRKS_MinusR :
    forall store n k ty_out,
      NStoreResolvedKontShape store k TyNat ty_out ->
      NStoreResolvedKontShape store (KMinusR n k) TyNat ty_out
| NSRKS_TimesL :
    forall store e2 env rho k gamma omega eff ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NStoreResolvedKontShape store k TyNat ty_out ->
      NStoreResolvedKontShape store
        (KTimesL e2 env rho k)
        TyNat
        ty_out
| NSRKS_TimesR :
    forall store n k ty_out,
      NStoreResolvedKontShape store k TyNat ty_out ->
      NStoreResolvedKontShape store (KTimesR n k) TyNat ty_out
| NSRKS_EqL :
    forall store e2 env rho k gamma omega eff ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NStoreResolvedKontShape store k TyBool ty_out ->
      NStoreResolvedKontShape store
        (KEqL e2 env rho k)
        TyNat
        ty_out
| NSRKS_EqR :
    forall store n k ty_out,
      NStoreResolvedKontShape store k TyBool ty_out ->
      NStoreResolvedKontShape store (KEqR n k) TyNat ty_out
| NSRKS_ReadConc :
    forall store k r ty ty_out,
      NStoreResolvedKontShape store k TyEffect ty_out ->
      NStoreResolvedKontShape store
        (KReadConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| NSRKS_WriteConc :
    forall store k r ty ty_out,
      NStoreResolvedKontShape store k TyEffect ty_out ->
      NStoreResolvedKontShape store
        (KWriteConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| NSRKS_ConcatL :
    forall store e2 env rho k gamma omega eff ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyEffect eff ->
      NStoreResolvedKontShape store k TyEffect ty_out ->
      NStoreResolvedKontShape store
        (KConcatL e2 env rho k)
        TyEffect
        ty_out
| NSRKS_ConcatR :
    forall store theta k ty_out,
      NStoreResolvedKontShape store k TyEffect ty_out ->
      NStoreResolvedKontShape store
        (KConcatR theta k)
        TyEffect
        ty_out.

Inductive NStoreResolvedStateShape :
    NStoreTyping -> NState -> NTy -> Prop :=
| NSRSS_Eval :
    forall store heap env rho e k gamma omega ty ty_res eff ty_out,
      NStoreResolvedRuntimeShape heap store env rho gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty ty_res ->
      NCheckedTcExp gamma omega e ty eff ->
      NStoreResolvedKontShape store k ty_res ty_out ->
      NStoreResolvedStateShape store (StEval heap env rho e k) ty_out
| NSRSS_Return :
    forall store heap v k ty ty_out,
      NStoreKeysBoundedByHeap heap store ->
      NStoreResolvedHeapShape heap store ->
      NStoreResolvedValShape store v ty ->
      NStoreResolvedKontShape store k ty ty_out ->
      NStoreResolvedStateShape store (StReturn heap v k) ty_out
| NSRSS_Done :
    forall store heap v ty,
      NStoreKeysBoundedByHeap heap store ->
      NStoreResolvedHeapShape heap store ->
      NStoreResolvedValShape store v ty ->
      NStoreResolvedStateShape store (StDone heap v) ty
| NSRSS_Error :
    forall store heap ty,
      NStoreKeysBoundedByHeap heap store ->
      NStoreResolvedHeapShape heap store ->
      NStoreResolvedStateShape store (StError heap) ty
| NSRSS_PairParRun :
    forall store left_state right_state phi_left phi_right k
      heap ty1 ty2 ty_out,
      state_heap left_state = heap ->
      state_heap right_state = heap ->
      NStoreResolvedStateShape store left_state ty1 ->
      NStoreResolvedStateShape store right_state ty2 ->
      NStoreResolvedKontShape store k (TyPair ty1 ty2) ty_out ->
      NStoreResolvedStateShape store
        (StPairParRun left_state right_state phi_left phi_right k)
        ty_out.

Lemma NStoreResolvedValShape_pair_inv :
  forall store v1 v2 ty,
    NStoreResolvedValShape store (VPair v1 v2) ty ->
    exists ty1 ty2,
      ty = TyPair ty1 ty2 /\
      NStoreResolvedValShape store v1 ty1 /\
      NStoreResolvedValShape store v2 ty2.
Proof.
  intros store v1 v2 ty HVal.
  inversion HVal; subst.
  exists ty1, ty2.
  repeat split; assumption || reflexivity.
Qed.

Lemma NStoreResolvedStateShape_done_inv :
  forall store heap v ty,
    NStoreResolvedStateShape store (StDone heap v) ty ->
    NStoreKeysBoundedByHeap heap store /\
    NStoreResolvedHeapShape heap store /\
    NStoreResolvedValShape store v ty.
Proof.
  intros store heap v ty HState.
  remember (StDone heap v) as state eqn:HStateEq.
  destruct HState; inversion HStateEq; subst.
  split.
  - assumption.
  - split.
    + assumption.
    + assumption.
Qed.

Lemma NStoreResolvedStateShape_done_summary_inv :
  forall store heap theta ty,
    NStoreResolvedStateShape store (StDone heap (VSummary theta)) ty ->
    ty = TyEffect /\
    NStoreKeysBoundedByHeap heap store /\
    NStoreResolvedHeapShape heap store.
Proof.
  intros store heap theta ty HState.
  destruct
    (NStoreResolvedStateShape_done_inv
      store heap (VSummary theta) ty HState)
    as (HBounded & HHeap & HVal).
  dependent destruction HVal.
  split; [reflexivity |].
  split; assumption.
Qed.

Lemma NStoreResolvedStateShape_done_pair_inv :
  forall store heap v1 v2 ty,
    NStoreResolvedStateShape store (StDone heap (VPair v1 v2)) ty ->
    exists ty1 ty2,
      ty = TyPair ty1 ty2 /\
      NStoreKeysBoundedByHeap heap store /\
      NStoreResolvedHeapShape heap store /\
      NStoreResolvedValShape store v1 ty1 /\
      NStoreResolvedValShape store v2 ty2.
Proof.
  intros store heap v1 v2 ty HState.
  destruct
    (NStoreResolvedStateShape_done_inv
      store heap (VPair v1 v2) ty HState)
    as (HBounded & HHeap & HVal).
  destruct
    (NStoreResolvedValShape_pair_inv store v1 v2 ty HVal)
    as (ty1 & ty2 & HTy & HVal1 & HVal2).
  exists ty1, ty2.
  split; [exact HTy |].
  split; [exact HBounded |].
  split; [exact HHeap |].
  split; assumption.
Qed.

Lemma NStoreResolvedValShape_closure_inv :
  forall store closure_env closure_rho f x ec ee ty,
    NStoreResolvedValShape store
      (VClosure closure_env closure_rho f x ec ee)
      ty ->
    exists gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      ty =
        TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res /\
      NStoreResolvedEnvShape store closure_rho closure_env gamma /\
      NRhoModels omega closure_rho /\
      NResolveTy closure_rho ty_arg ty_arg_res /\
      NResolveStaticEffect closure_rho eff_body eff_body_res /\
      NResolveTy closure_rho ty_body ty_body_res /\
      NResolveStaticEffect closure_rho eff_summary eff_summary_res /\
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body /\
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary /\
      NCheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
      omega ec ee.
Proof.
  intros store closure_env closure_rho f x ec ee ty HVal.
  dependent destruction HVal.
  exists gamma, omega, ty_arg, ty_arg_res, ty_body, ty_body_res.
  exists eff_body, eff_body_res, eff_summary, eff_summary_res.
  split; [reflexivity |].
  split; [eassumption |].
  split; [eassumption |].
  split; [eassumption |].
  split; [eassumption |].
  split; [eassumption |].
  split; [eassumption |].
  split; [eassumption |].
  split; [eassumption |].
  eassumption.
Qed.

Lemma NStoreResolvedValShape_region_closure_inv :
  forall store closure_env closure_rho x e ty_final,
    NStoreResolvedValShape store
      (VRegionClosure closure_env closure_rho x e)
      ty_final ->
    exists gamma omega ty_body ty_res eff eff_res,
      ty_final = TyForallRgn eff_res ty_res /\
      NStoreResolvedEnvShape store closure_rho closure_env gamma /\
      NRhoModels omega closure_rho /\
      NResolveStaticEffect closure_rho
        (close_static_effect x eff) eff_res /\
      NResolveTy closure_rho (close_ty x ty_body) ty_res /\
      NCheckedRegionBody x gamma omega e ty_body eff.
Proof.
  intros store closure_env closure_rho x e ty_final HVal.
  dependent destruction HVal.
  exists gamma, omega, ty, ty_res, eff, eff_res.
  split; [reflexivity |].
  split; [eassumption |].
  split; [eassumption |].
  split; [eassumption |].
  split; [eassumption |].
  eassumption.
Qed.

Lemma NStoreResolvedStateShape_done_closure_inv :
  forall store heap closure_env closure_rho f x ec ee ty,
    NStoreResolvedStateShape store
      (StDone heap (VClosure closure_env closure_rho f x ec ee))
      ty ->
    exists gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      NStoreKeysBoundedByHeap heap store /\
      NStoreResolvedHeapShape heap store /\
      ty =
        TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res /\
      NStoreResolvedEnvShape store closure_rho closure_env gamma /\
      NRhoModels omega closure_rho /\
      NResolveTy closure_rho ty_arg ty_arg_res /\
      NResolveStaticEffect closure_rho eff_body eff_body_res /\
      NResolveTy closure_rho ty_body ty_body_res /\
      NResolveStaticEffect closure_rho eff_summary eff_summary_res /\
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body /\
      NCheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary /\
      NCheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee.
Proof.
  intros store heap closure_env closure_rho f x ec ee ty HState.
  destruct
    (NStoreResolvedStateShape_done_inv
      store heap
      (VClosure closure_env closure_rho f x ec ee)
      ty
      HState)
    as (HBounded & HHeap & HVal).
  destruct
    (NStoreResolvedValShape_closure_inv
      store closure_env closure_rho f x ec ee ty HVal)
    as
      (gamma & omega & ty_arg & ty_arg_res & ty_body & ty_body_res &
        eff_body & eff_body_res & eff_summary & eff_summary_res &
        HTy & HEnv & HRho & HArgResolve & HBodyResolve &
        HBodyTyResolve & HSummaryResolve & HBodyTc & HSummaryTc &
        HBodyBack).
  exists gamma, omega, ty_arg, ty_arg_res, ty_body, ty_body_res.
  exists eff_body, eff_body_res, eff_summary, eff_summary_res.
  split; [exact HBounded |].
  split; [exact HHeap |].
  split; [exact HTy |].
  split; [exact HEnv |].
  split; [exact HRho |].
  split; [exact HArgResolve |].
  split; [exact HBodyResolve |].
  split; [exact HBodyTyResolve |].
  split; [exact HSummaryResolve |].
  split; [exact HBodyTc |].
  split; [exact HSummaryTc |].
  exact HBodyBack.
Qed.

Lemma NStoreResolvedStateShape_aligned :
  forall store state ty,
    NStoreResolvedStateShape store state ty ->
    NStateHeapsAligned state.
Proof.
  intros store state ty HState.
  induction HState; simpl; try exact I.
  repeat split; assumption || congruence.
Qed.

Lemma NStoreResolvedStateShape_with_state_heap_same :
  forall store state ty heap,
    NStoreResolvedStateShape store state ty ->
    state_heap state = heap ->
    NStoreResolvedStateShape store (with_state_heap heap state) ty.
Proof.
  intros store state ty heap HState HHeap.
  rewrite (with_state_heap_aligned_same heap state).
  - exact HState.
  - eapply NStoreResolvedStateShape_aligned; eauto.
  - exact HHeap.
Qed.

Lemma NStoreResolvedStateShape_initial :
  forall heap store env rho e gamma omega ty ty_res eff,
    NStoreResolvedRuntimeShape heap store env rho gamma ->
    NRhoModels omega rho ->
    NResolveTy rho ty ty_res ->
    NCheckedTcExp gamma omega e ty eff ->
    NStoreResolvedStateShape store (NInitialState heap env rho e) ty_res.
Proof.
  intros heap store env rho e gamma omega ty ty_res eff
    HRuntime HRho HResolve HChecked.
  unfold NInitialState.
  eapply NSRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty) (eff := eff);
    eauto.
  constructor.
Qed.

Lemma NStoreKeysBoundedByHeap_update :
  forall heap store r l v,
    NStoreKeysBoundedByHeap heap store ->
    NStoreKeysBoundedByHeap (heap_update r l v heap) store.
Proof.
  intros heap store r l v HBounded r' l' ty HIn.
  rewrite heap_update_length.
  eapply HBounded; eauto.
Qed.

Lemma NStoreResolvedHeapShape_update :
  forall heap store r l old v ty,
    NStoreResolvedHeapShape heap store ->
    heap_lookup r l heap = Some old ->
    store_ty_lookup r l store = Some ty ->
    NStoreResolvedValShape store v ty ->
    NStoreResolvedHeapShape (heap_update r l v heap) store.
Proof.
  intros heap store r l old v ty
    [HHeapToStore HStoreToHeap] HOldLookup HStoreLookup HVal.
  split.
  - intros r' l' v' HLookup.
    destruct (Nat.eq_dec r' r) as [HR | HR];
      destruct (Nat.eq_dec l' l) as [HL | HL];
      subst.
    + pose proof
        (heap_update_lookup_same heap r l v)
        as HSame.
      assert (heap_lookup r l heap <> None) as HSome.
      {
        rewrite HOldLookup. discriminate.
      }
      specialize (HSame HSome).
      rewrite HSame in HLookup.
      inversion HLookup; subst.
      exists ty. split; assumption.
    + rewrite heap_update_lookup_other in HLookup by auto.
      eapply HHeapToStore; eauto.
    + rewrite heap_update_lookup_other in HLookup by auto.
      eapply HHeapToStore; eauto.
    + rewrite heap_update_lookup_other in HLookup by auto.
      eapply HHeapToStore; eauto.
  - intros r' l' ty' HStoreLookup'.
    destruct (HStoreToHeap r' l' ty' HStoreLookup')
      as (old' & HOldLookup' & HOldShape).
    destruct (Nat.eq_dec r' r) as [HR | HR];
      destruct (Nat.eq_dec l' l) as [HL | HL];
      subst.
    + pose proof
        (store_ty_lookup_deterministic
          store r l ty' ty HStoreLookup' HStoreLookup)
        as HTyEq.
      subst ty'.
      exists v. split; [| exact HVal].
      eapply heap_update_lookup_same.
      rewrite HOldLookup. discriminate.
    + exists old'. split; [| exact HOldShape].
      rewrite heap_update_lookup_other by auto.
      exact HOldLookup'.
    + exists old'. split; [| exact HOldShape].
      rewrite heap_update_lookup_other by auto.
      exact HOldLookup'.
    + exists old'. split; [| exact HOldShape].
      rewrite heap_update_lookup_other by auto.
      exact HOldLookup'.
Qed.

Lemma NStoreResolvedRuntimeShape_update :
  forall heap store env rho gamma r l old v ty,
    NStoreResolvedRuntimeShape heap store env rho gamma ->
    heap_lookup r l heap = Some old ->
    store_ty_lookup r l store = Some ty ->
    NStoreResolvedValShape store v ty ->
    NStoreResolvedRuntimeShape
      (heap_update r l v heap)
      store env rho gamma.
Proof.
  intros heap store env rho gamma r l old v ty
    (HBounded & HHeap & HEnv) HOldLookup HStoreLookup HVal.
  split.
  - eapply NStoreKeysBoundedByHeap_update; eauto.
  - split.
    + eapply NStoreResolvedHeapShape_update; eauto.
    + exact HEnv.
Qed.

Lemma NStoreResolvedValShape_store_extend :
  forall heap store r_new l_new ty_new v ty,
    NStoreKeysBoundedByHeap heap store ->
    l_new = length heap ->
    NStoreResolvedValShape store v ty ->
    NStoreResolvedValShape ((r_new, l_new, ty_new) :: store) v ty
with NStoreResolvedEnvShape_store_extend :
  forall heap store r_new l_new ty_new rho env gamma,
    NStoreKeysBoundedByHeap heap store ->
    l_new = length heap ->
    NStoreResolvedEnvShape store rho env gamma ->
    NStoreResolvedEnvShape ((r_new, l_new, ty_new) :: store) rho env gamma.
Proof.
  - intros heap store r_new l_new ty_new v ty
      HBounded HFresh HVal.
    induction HVal.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + eapply NSRVS_Pair; eauto.
    + eapply NSRVS_Loc.
      eapply store_ty_lookup_extend_old; eauto.
    + eapply NSRVS_Closure with
        (gamma := gamma) (omega := omega)
        (ty_arg := ty_arg) (ty_body := ty_body);
        eauto.
    + eapply NSRVS_RegionClosure with
        (gamma := gamma) (omega := omega);
        eauto.
  - intros heap store r_new l_new ty_new rho env gamma
      HBounded HFresh HEnv.
    induction HEnv.
    + constructor.
    + econstructor; eauto.
Qed.

Lemma NStoreResolvedKontShape_store_extend :
  forall heap store r_new l_new ty_new k ty_in ty_out,
    NStoreKeysBoundedByHeap heap store ->
    l_new = length heap ->
    NStoreResolvedKontShape store k ty_in ty_out ->
    NStoreResolvedKontShape
      ((r_new, l_new, ty_new) :: store) k ty_in ty_out.
Proof.
  intros heap store r_new l_new ty_new k ty_in ty_out
    HBounded HFresh HK.
  induction HK; try solve [econstructor; eauto].
  - eapply NSRKS_MuAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_MuAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_EffAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_EffAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_PairParEff1 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2)
      (eff_summary2 := eff_summary2);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_PairParEff2 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_Cond with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_t := eff_t) (eff_f := eff_f);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_AssignLoc with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_v := eff_v);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_AssignVal; eauto.
    eapply NStoreResolvedValShape_store_extend; eauto.
  - eapply NSRKS_PlusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_MinusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_TimesL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_EqL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using NStoreResolvedEnvShape_store_extend.
  - eapply NSRKS_ConcatL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using NStoreResolvedEnvShape_store_extend.
Qed.

Lemma NStoreKeysBoundedByHeap_alloc :
  forall heap store r_new l_new v_new ty_new heap',
    NStoreKeysBoundedByHeap heap store ->
    heap_alloc r_new v_new heap = (l_new, heap') ->
    NStoreKeysBoundedByHeap
      heap' ((r_new, l_new, ty_new) :: store).
Proof.
  intros heap store r_new l_new v_new ty_new heap'
    HBounded HAlloc.
  destruct (heap_alloc_result heap r_new v_new l_new heap')
    as [-> ->]; [exact HAlloc |].
  intros r l ty HIn.
  simpl in HIn.
  destruct HIn as [HIn | HIn].
  - inversion HIn; subst. simpl. lia.
  - simpl. specialize (HBounded r l ty HIn). lia.
Qed.

Lemma NStoreResolvedHeapShape_alloc :
  forall heap store r_new v_new ty_new l_new heap',
    NStoreKeysBoundedByHeap heap store ->
    NStoreResolvedHeapShape heap store ->
    NStoreResolvedValShape store v_new ty_new ->
    heap_alloc r_new v_new heap = (l_new, heap') ->
    NStoreResolvedHeapShape
      heap' ((r_new, l_new, ty_new) :: store).
Proof.
  intros heap store r_new v_new ty_new l_new heap'
    HBounded [HHeapToStore HStoreToHeap] HValNew HAlloc.
  destruct (heap_alloc_result heap r_new v_new l_new heap')
    as [-> ->]; [exact HAlloc |].
  split.
  - intros r l v HLookup.
    simpl in HLookup.
    destruct (Nat.eqb r r_new && Nat.eqb l (length heap)) eqn:HEq.
    + inversion HLookup; subst.
      apply andb_true_iff in HEq.
      destruct HEq as [HR HL].
      apply Nat.eqb_eq in HR.
      apply Nat.eqb_eq in HL.
      subst r l.
      exists ty_new.
      split.
      * apply store_ty_lookup_extend_same.
      * eapply NStoreResolvedValShape_store_extend; eauto.
    + destruct (HHeapToStore r l v HLookup) as
        (ty & HStoreLookup & HShape).
      exists ty.
      split.
      * eapply store_ty_lookup_extend_old; eauto.
      * eapply NStoreResolvedValShape_store_extend; eauto.
  - intros r l ty HStoreLookup.
    simpl in HStoreLookup.
    destruct (Nat.eqb r r_new && Nat.eqb l (length heap)) eqn:HEq.
    + apply andb_true_iff in HEq.
      destruct HEq as [HR HL].
      apply Nat.eqb_eq in HR.
      apply Nat.eqb_eq in HL.
      inversion HStoreLookup; subst.
      exists v_new.
      split.
      * simpl. rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
      * eapply NStoreResolvedValShape_store_extend; eauto.
    + destruct (HStoreToHeap r l ty HStoreLookup) as
        (v & HHeapLookup & HShape).
      exists v.
      split.
      * simpl. rewrite HEq. exact HHeapLookup.
      * eapply NStoreResolvedValShape_store_extend; eauto.
Qed.

Lemma NStoreResolvedRuntimeShape_alloc :
  forall heap store env rho gamma r_new v_new ty_new l_new heap',
    NStoreResolvedRuntimeShape heap store env rho gamma ->
    NStoreResolvedValShape store v_new ty_new ->
    heap_alloc r_new v_new heap = (l_new, heap') ->
    NStoreResolvedRuntimeShape
      heap' ((r_new, l_new, ty_new) :: store) env rho gamma.
Proof.
  intros heap store env rho gamma r_new v_new ty_new l_new heap'
    (HBounded & HHeap & HEnv) HValNew HAlloc.
  split.
  - eapply NStoreKeysBoundedByHeap_alloc; eauto.
  - split.
    + eapply NStoreResolvedHeapShape_alloc; eauto.
    + destruct (heap_alloc_result heap r_new v_new l_new heap')
        as [HFresh _]; [exact HAlloc |].
      eapply NStoreResolvedEnvShape_store_extend; eauto.
Qed.

Lemma NStoreResolvedStateShape_heap_update :
  forall state store ty heap r l old v ty_cell,
    state_heap state = heap ->
    heap_lookup r l heap = Some old ->
    store_ty_lookup r l store = Some ty_cell ->
    NStoreResolvedValShape store v ty_cell ->
    NStoreResolvedStateShape store state ty ->
    NStoreResolvedStateShape store
      (with_state_heap (heap_update r l v heap) state) ty.
Proof.
  intros state store ty heap r l old v ty_cell
    HStateHeap HOldLookup HStoreLookup HVal HState.
  revert heap r l old v ty_cell
    HStateHeap HOldLookup HStoreLookup HVal.
  induction HState;
    intros heap_current r_update l_update old v_update ty_cell
      HStateHeap HOldLookup HStoreLookup HVal;
    simpl in HStateHeap.
  - subst heap_current.
    simpl.
    eapply NSRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty) (eff := eff);
      eauto.
    eapply NStoreResolvedRuntimeShape_update; eauto.
  - subst heap_current.
    simpl.
    eapply NSRSS_Return with (ty := ty);
      eauto using
        NStoreKeysBoundedByHeap_update,
        NStoreResolvedHeapShape_update.
  - subst heap_current.
    simpl.
    eapply NSRSS_Done with (ty := ty);
      eauto using
        NStoreKeysBoundedByHeap_update,
        NStoreResolvedHeapShape_update.
  - subst heap_current.
    simpl.
    eapply NSRSS_Error;
      eauto using
        NStoreKeysBoundedByHeap_update,
        NStoreResolvedHeapShape_update.
  - simpl.
    pose proof
      (NStoreResolvedStateShape_aligned _ _ _ HState1)
      as HAlignedLeft.
    pose proof
      (NStoreResolvedStateShape_aligned _ _ _ HState2)
      as HAlignedRight.
    destruct
      (with_state_heap_aligned
        (heap_update r_update l_update v_update heap_current)
        left_state HAlignedLeft)
      as (_ & HLeftHeap').
    destruct
      (with_state_heap_aligned
        (heap_update r_update l_update v_update heap_current)
        right_state HAlignedRight)
      as (_ & HRightHeap').
    assert (HLeftHeap : state_heap left_state = heap_current)
      by exact HStateHeap.
    assert (HRightHeap : state_heap right_state = heap_current).
    {
      rewrite H0.
      rewrite <- H.
      exact HStateHeap.
    }
    eapply NSRSS_PairParRun with
      (heap := heap_update r_update l_update v_update heap_current)
      (ty1 := ty1) (ty2 := ty2).
    + exact HLeftHeap'.
    + exact HRightHeap'.
    + eapply IHHState1; eauto.
    + eapply IHHState2; eauto.
    + eauto.
Qed.

Lemma NStoreResolvedStateShape_heap_alloc :
  forall state store ty heap r_alloc v_alloc ty_alloc l_alloc heap',
    NStoreKeysBoundedByHeap heap store ->
    state_heap state = heap ->
    NStoreResolvedValShape store v_alloc ty_alloc ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    NStoreResolvedStateShape store state ty ->
    NStoreResolvedStateShape
      ((r_alloc, l_alloc, ty_alloc) :: store)
      (with_state_heap heap' state)
      ty.
Proof.
  intros state store ty heap r_alloc v_alloc ty_alloc l_alloc heap'
    HBounded HStateHeap HAllocVal HAlloc HState.
  revert heap r_alloc v_alloc ty_alloc l_alloc heap'
    HBounded HStateHeap HAllocVal HAlloc.
  induction HState;
    intros heap_current r_alloc v_alloc ty_alloc l_alloc heap'
      HBounded HStateHeap HAllocVal HAlloc;
    simpl in HStateHeap.
  - subst heap_current.
    simpl.
    eapply NSRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty) (eff := eff).
    + eapply NStoreResolvedRuntimeShape_alloc; eauto.
    + eauto.
    + eauto.
    + eauto.
    + destruct (heap_alloc_result heap r_alloc v_alloc l_alloc heap')
        as [HFresh _]; [exact HAlloc |].
      eapply NStoreResolvedKontShape_store_extend; eauto.
  - subst heap_current.
    simpl.
    eapply NSRSS_Return with (ty := ty).
    + eapply NStoreKeysBoundedByHeap_alloc; eauto.
    + eapply NStoreResolvedHeapShape_alloc; eauto.
    + destruct (heap_alloc_result heap r_alloc v_alloc l_alloc heap')
        as [HFresh _]; [exact HAlloc |].
      eapply NStoreResolvedValShape_store_extend; eauto.
    + destruct (heap_alloc_result heap r_alloc v_alloc l_alloc heap')
        as [HFresh _]; [exact HAlloc |].
      eapply NStoreResolvedKontShape_store_extend; eauto.
  - subst heap_current.
    simpl.
    eapply NSRSS_Done with (ty := ty).
    + eapply NStoreKeysBoundedByHeap_alloc; eauto.
    + eapply NStoreResolvedHeapShape_alloc; eauto.
    + destruct (heap_alloc_result heap r_alloc v_alloc l_alloc heap')
        as [HFresh _]; [exact HAlloc |].
      eapply NStoreResolvedValShape_store_extend; eauto.
  - subst heap_current.
    simpl.
    eapply NSRSS_Error.
    + eapply NStoreKeysBoundedByHeap_alloc; eauto.
    + eapply NStoreResolvedHeapShape_alloc; eauto.
  - simpl.
    pose proof
      (NStoreResolvedStateShape_aligned _ _ _ HState1)
      as HAlignedLeft.
    pose proof
      (NStoreResolvedStateShape_aligned _ _ _ HState2)
      as HAlignedRight.
    destruct
      (with_state_heap_aligned heap' left_state HAlignedLeft)
      as (_ & HLeftHeap').
    destruct
      (with_state_heap_aligned heap' right_state HAlignedRight)
      as (_ & HRightHeap').
    assert (HLeftHeap : state_heap left_state = heap_current)
      by exact HStateHeap.
    assert (HRightHeap : state_heap right_state = heap_current).
    {
      rewrite H0.
      rewrite <- H.
      exact HStateHeap.
    }
    eapply NSRSS_PairParRun with
      (heap := heap') (ty1 := ty1) (ty2 := ty2).
    + exact HLeftHeap'.
    + exact HRightHeap'.
    + eapply IHHState1; eauto.
    + eapply IHHState2; eauto.
    + destruct (heap_alloc_result heap_current r_alloc v_alloc l_alloc heap')
        as [HFresh _]; [exact HAlloc |].
      eapply NStoreResolvedKontShape_store_extend; eauto.
Qed.

Lemma NRegularResolvedValShape_heap_alloc :
  forall heap r_alloc v_alloc l_alloc heap' v ty,
    NHeapKeysBounded heap ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    NRegularResolvedValShape heap v ty ->
    NRegularResolvedValShape heap' v ty
with NRegularResolvedEnvShape_heap_alloc :
  forall rho heap env gamma r_alloc v_alloc l_alloc heap',
    NHeapKeysBounded heap ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    NRegularResolvedEnvShape rho heap env gamma ->
    NRegularResolvedEnvShape rho heap' env gamma.
Proof.
  - intros heap r_alloc v_alloc l_alloc heap' v ty
      HBounded HAlloc HVal.
    induction HVal.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + eapply NRRVS_Pair; eauto.
    + eapply NRRVS_Loc; eauto.
      eapply heap_lookup_alloc_old; eauto.
    + eapply NRRVS_Closure with
        (gamma := gamma) (omega := omega)
        (ty_arg := ty_arg) (ty_body := ty_body);
        eauto.
    + eapply NRRVS_RegionClosure with
        (gamma := gamma) (omega := omega);
        eauto.
  - intros rho heap env gamma r_alloc v_alloc l_alloc heap'
      HBounded HAlloc HEnv.
    induction HEnv.
    + constructor.
    + econstructor; eauto.
Qed.

Lemma NRegularResolvedHeapShape_alloc :
  forall heap r_alloc v_alloc ty_alloc l_alloc heap',
    NHeapKeysBounded heap ->
    NRegularResolvedHeapShape heap ->
    NRegularResolvedValShape heap v_alloc ty_alloc ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    NRegularResolvedHeapShape heap'.
Proof.
  intros heap r_alloc v_alloc ty_alloc l_alloc heap'
    HBounded HHeap HAllocVal HAlloc.
  pose proof HAlloc as HAllocShape.
  destruct
    (heap_alloc_result heap r_alloc v_alloc l_alloc heap' HAlloc)
    as [-> ->].
  unfold NRegularResolvedHeapShape in *.
  intros r l v HLookup.
  simpl in HLookup.
  destruct (Nat.eqb r r_alloc && Nat.eqb l (length heap)) eqn:HEq.
  - inversion HLookup; subst.
    exists ty_alloc.
    eapply NRegularResolvedValShape_heap_alloc; eauto.
  - destruct (HHeap r l v HLookup) as (ty & HVal).
    exists ty.
    eapply NRegularResolvedValShape_heap_alloc; eauto.
Qed.

Lemma NRegularResolvedKontShape_heap_alloc :
  forall heap r_alloc v_alloc ty_alloc l_alloc heap' k ty_in ty_out,
    NHeapKeysBounded heap ->
    NRegularResolvedValShape heap v_alloc ty_alloc ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    NRegularResolvedKontShape heap k ty_in ty_out ->
    NRegularResolvedKontShape heap' k ty_in ty_out.
Proof.
  intros heap r_alloc v_alloc ty_alloc l_alloc heap' k ty_in ty_out
    HBounded HAllocVal HAlloc HK.
  induction HK; try solve [econstructor; eauto].
  - eapply NRRKS_MuAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_MuAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_EffAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_EffAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_PairParEff1 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2)
      (eff_summary2 := eff_summary2);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_PairParEff2 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_Cond with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_t := eff_t) (eff_f := eff_f);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_AssignLoc with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_v := eff_v);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_AssignVal; eauto.
    eapply NRegularResolvedValShape_heap_alloc; eauto.
  - eapply NRRKS_PlusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_MinusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_TimesL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_EqL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using NRegularResolvedEnvShape_heap_alloc.
  - eapply NRRKS_ConcatL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using NRegularResolvedEnvShape_heap_alloc.
Qed.

Lemma NRegularResolvedStateShape_heap_alloc :
  forall state ty heap r_alloc v_alloc ty_alloc l_alloc heap',
    NHeapKeysBounded heap ->
    state_heap state = heap ->
    NRegularResolvedValShape heap v_alloc ty_alloc ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    NRegularResolvedStateShape state ty ->
    NRegularResolvedStateShape (with_state_heap heap' state) ty.
Proof.
  intros state ty heap r_alloc v_alloc ty_alloc l_alloc heap'
    HBounded HStateHeap HAllocVal HAlloc HState.
  revert heap r_alloc v_alloc ty_alloc l_alloc heap'
    HBounded HStateHeap HAllocVal HAlloc.
  induction HState;
    intros heap_current r_alloc v_alloc ty_alloc l_alloc heap'
      HBounded HStateHeap HAllocVal HAlloc;
    simpl in HStateHeap.
  - subst heap_current.
    simpl.
    eapply NRRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty) (eff := eff);
      eauto using
        NRegularResolvedHeapShape_alloc,
        NRegularResolvedEnvShape_heap_alloc,
        NRegularResolvedKontShape_heap_alloc.
  - subst heap_current.
    simpl.
    eapply NRRSS_Return with (ty := ty);
      eauto using
        NRegularResolvedHeapShape_alloc,
        NRegularResolvedValShape_heap_alloc,
        NRegularResolvedKontShape_heap_alloc.
  - subst heap_current.
    simpl.
    eapply NRRSS_Done with (ty := ty);
      eauto using
        NRegularResolvedHeapShape_alloc,
        NRegularResolvedValShape_heap_alloc.
  - subst heap_current.
    simpl.
    eapply NRRSS_Error;
      eauto using NRegularResolvedHeapShape_alloc.
  - simpl.
    pose proof
      (NRegularResolvedStateShape_aligned _ _ HState1)
      as HAlignedLeft.
    pose proof
      (NRegularResolvedStateShape_aligned _ _ HState2)
      as HAlignedRight.
    destruct
      (with_state_heap_aligned heap' left_state HAlignedLeft)
      as (_ & HLeftHeap').
    destruct
      (with_state_heap_aligned heap' right_state HAlignedRight)
      as (_ & HRightHeap').
    assert (HLeftHeap : state_heap left_state = heap_current)
      by exact HStateHeap.
    assert (HRightHeap : state_heap right_state = heap_current).
    {
      rewrite H0.
      rewrite <- H.
      exact HStateHeap.
    }
    assert (HShapeHeap : heap = heap_current) by congruence.
    subst heap.
    eapply NRRSS_PairParRun with
      (heap := heap') (ty1 := ty1) (ty2 := ty2).
    + exact HLeftHeap'.
    + exact HRightHeap'.
    + eapply IHHState1; eauto.
    + eapply IHHState2; eauto.
    + eapply NRegularResolvedKontShape_heap_alloc; eauto.
      rewrite <- HShapeHeap. exact H1.
Qed.
