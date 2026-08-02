From Stdlib Require Import List.
From Stdlib Require Import Ascii.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Program.Equality.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.HeapFacts.
Require Import theories.SmallStep.Runtime.HeapNeutral.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Runtime.StateShape.
Require Import theories.SmallStep.Runtime.Typing.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Regularity.
Require Import theories.SmallStep.Typing.Resolve.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.

Inductive RegularResolvedValShape : Heap -> Val -> Ty -> Prop :=
| RRVS_Nat :
    forall heap n,
      RegularResolvedValShape heap (VNat n) TyNat
| RRVS_Bool :
    forall heap b,
      RegularResolvedValShape heap (VBool b) TyBool
| RRVS_Unit :
    forall heap,
      RegularResolvedValShape heap VUnit TyUnit
| RRVS_Summary :
    forall heap theta,
      RegularResolvedValShape heap (VSummary theta) TyEffect
| RRVS_Pair :
    forall heap v1 v2 ty1 ty2,
      RegularResolvedValShape heap v1 ty1 ->
      RegularResolvedValShape heap v2 ty2 ->
      RegularResolvedValShape heap (VPair v1 v2) (TyPair ty1 ty2)
| RRVS_Loc :
    forall heap r l cell ty,
      heap_lookup r l heap = Some cell ->
      RegularResolvedValShape heap cell ty ->
      RegularResolvedValShape heap
        (VLoc r l)
        (TyRef (region_const_type r) ty)
| RRVS_Closure :
    forall heap closure_env closure_rho f x ec ee
      gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      RegularResolvedEnvShape closure_rho heap closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveTy closure_rho ty_arg ty_arg_res ->
      ResolveStaticEffect closure_rho eff_body eff_body_res ->
      ResolveTy closure_rho ty_body ty_body_res ->
      ResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      CheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      RegularResolvedValShape heap
        (VClosure closure_env closure_rho f x ec ee)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
| RRVS_RegionClosure :
    forall heap closure_env closure_rho x e gamma omega ty ty_res eff eff_res,
      RegularResolvedEnvShape closure_rho heap closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveStaticEffect closure_rho (close_static_effect x eff) eff_res ->
      ResolveTy closure_rho (close_ty x ty) ty_res ->
      CheckedRegionBody x gamma omega e ty eff ->
      RegularResolvedValShape heap
        (VRegionClosure closure_env closure_rho x e)
        (TyForallRgn eff_res ty_res)
with RegularResolvedEnvShape : Rho -> Heap -> Env -> Ctx -> Prop :=
| RRES_EnvNil :
    forall rho heap,
      RegularResolvedEnvShape rho heap EnvNil []
| RRES_EnvCons :
    forall rho heap x v env ty ty_res gamma,
      ResolveTy rho ty ty_res ->
      RegularResolvedValShape heap v ty_res ->
      RegularResolvedEnvShape rho heap env gamma ->
      RegularResolvedEnvShape rho heap (EnvCons x v env) ((x, ty) :: gamma).

Scheme RegularResolvedValShape_ind' :=
  Induction for RegularResolvedValShape Sort Prop
with RegularResolvedEnvShape_ind' :=
  Induction for RegularResolvedEnvShape Sort Prop.

Combined Scheme RegularResolvedValShape_RegularResolvedEnvShape_ind
  from RegularResolvedValShape_ind', RegularResolvedEnvShape_ind'.

Lemma RegularResolvedEnvShape_lookup :
  forall rho heap env gamma x ty ty_res,
    RegularResolvedEnvShape rho heap env gamma ->
    ctx_binds x ty gamma ->
    ResolveTy rho ty ty_res ->
    exists v,
      env_lookup x env = Some v /\
      RegularResolvedValShape heap v ty_res.
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
        HVStored : RegularResolvedValShape heap v ?ty_stored |- _ =>
          pose proof
            (ResolveTy_deterministic
              rho ty ty_stored ty_goal HStored HGoal)
            as HResolvedEq;
          subst ty_goal;
          exists v; split; [reflexivity | exact HVStored]
      end.
    + apply IH; assumption.
Qed.

Lemma RegularResolvedEnvShape_extend :
  forall rho heap env gamma x v ty ty_res,
    ResolveTy rho ty ty_res ->
    RegularResolvedValShape heap v ty_res ->
    RegularResolvedEnvShape rho heap env gamma ->
    RegularResolvedEnvShape rho heap
      (env_extend x v env)
      ((x, ty) :: gamma).
Proof.
  intros rho heap env gamma x v ty ty_res HResolve HVal HEnv.
  eapply RRES_EnvCons; eauto.
Qed.

Lemma RegularResolvedEnvShape_extend_fresh :
  forall rho heap env gamma omega x r_val,
    ~ In x omega ->
    CtxWF omega gamma ->
    RegularResolvedEnvShape rho heap env gamma ->
    RegularResolvedEnvShape (rho_extend x r_val rho) heap env gamma.
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

Definition RegularResolvedHeapShape (heap : Heap) : Prop :=
  forall r l v,
    heap_lookup r l heap = Some v ->
    exists ty,
      RegularResolvedValShape heap v ty.

Lemma RegularResolvedHeapShape_lookup :
  forall heap r l v,
    RegularResolvedHeapShape heap ->
    heap_lookup r l heap = Some v ->
    exists ty,
      RegularResolvedValShape heap v ty.
Proof.
  intros heap r l v HHeap HLookup.
  exact (HHeap r l v HLookup).
Qed.

Inductive RegularResolvedKontShape :
    Heap -> Kont -> Ty -> Ty -> Prop :=
| RRKS_Done :
    forall heap ty,
      RegularResolvedKontShape heap KDone ty ty
| RRKS_MuAppFun :
    forall heap ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty_arg ty_arg_res ->
      ResolveStaticEffect rho eff_body eff_body_res ->
      ResolveTy rho ty_body ty_body_res ->
      ResolveStaticEffect rho eff_summary eff_summary_res ->
      CheckedTcExp gamma omega ea ty_arg eff_arg ->
      RegularResolvedKontShape heap k ty_body_res ty_out ->
      RegularResolvedKontShape heap
        (KMuAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| RRKS_MuAppArg :
    forall heap closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      RegularResolvedEnvShape closure_rho heap closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveTy closure_rho ty_arg ty_arg_res ->
      ResolveStaticEffect closure_rho eff_body eff_body_res ->
      ResolveTy closure_rho ty_body ty_body_res ->
      ResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      CheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      RegularResolvedKontShape heap k ty_body_res ty_out ->
      RegularResolvedKontShape heap
        (KMuAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| RRKS_EffAppFun :
    forall heap ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty_arg ty_arg_res ->
      ResolveStaticEffect rho eff_body eff_body_res ->
      ResolveTy rho ty_body ty_body_res ->
      ResolveStaticEffect rho eff_summary eff_summary_res ->
      CheckedTcExp gamma omega ea ty_arg eff_arg ->
      RegularResolvedKontShape heap k TyEffect ty_out ->
      RegularResolvedKontShape heap
        (KEffAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| RRKS_EffAppArg :
    forall heap closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      RegularResolvedEnvShape closure_rho heap closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveTy closure_rho ty_arg ty_arg_res ->
      ResolveStaticEffect closure_rho eff_body eff_body_res ->
      ResolveTy closure_rho ty_body ty_body_res ->
      ResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      CheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      RegularResolvedKontShape heap k TyEffect ty_out ->
      RegularResolvedKontShape heap
        (KEffAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| RRKS_PairParEff1 :
    forall heap ef1 ea1 ef2 ea2 env rho k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 eff_summary2 ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty1 ty1_res ->
      ResolveTy rho ty2 ty2_res ->
      CheckedTcExp gamma omega
        (EMuApp ef1 ea1) ty1 eff1 ->
      CheckedTcExp gamma omega
        (EMuApp ef2 ea2) ty2 eff2 ->
      CheckedTcExp gamma omega
        (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      RegularResolvedKontShape heap k (TyPair ty1_res ty2_res) ty_out ->
      RegularResolvedKontShape heap
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
        TyEffect
        ty_out
| RRKS_PairParEff2 :
    forall heap ef1 ea1 ef2 ea2 env rho theta1 k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty1 ty1_res ->
      ResolveTy rho ty2 ty2_res ->
      CheckedTcExp gamma omega
        (EMuApp ef1 ea1) ty1 eff1 ->
      CheckedTcExp gamma omega
        (EMuApp ef2 ea2) ty2 eff2 ->
      RegularResolvedKontShape heap k (TyPair ty1_res ty2_res) ty_out ->
      RegularResolvedKontShape heap
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
        TyEffect
        ty_out
| RRKS_PairParFallbackLeft :
    forall heap ef2 ea2 env rho k gamma omega
      ty_left_res ty2 ty2_res eff2 ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty2 ty2_res ->
      CheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      RegularResolvedKontShape heap k
        (TyPair ty_left_res ty2_res) ty_out ->
      RegularResolvedKontShape heap
        (KPairParFallbackLeft ef2 ea2 env rho k)
        ty_left_res
        ty_out
| RRKS_PairParFallbackRight :
    forall heap v_left k ty_left_res ty2_res ty_out,
      RegularResolvedValShape heap v_left ty_left_res ->
      RegularResolvedKontShape heap k
        (TyPair ty_left_res ty2_res) ty_out ->
      RegularResolvedKontShape heap
        (KPairParFallbackRight v_left k)
        ty2_res
        ty_out
| RRKS_RgnApp :
    forall heap r arg_rho r_val k eff ty ty_out,
      eval_region arg_rho r = Some r_val ->
      RegularResolvedKontShape heap k
        (open_ty_type (region_const_type r_val) ty)
        ty_out ->
      RegularResolvedKontShape heap
        (KRgnApp r arg_rho k)
        (TyForallRgn eff ty)
        ty_out
| RRKS_Cond :
    forall heap et ef env rho k gamma omega ty ty_res eff_t eff_f ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty ty_res ->
      CheckedTcExp gamma omega et ty eff_t ->
      CheckedTcExp gamma omega ef ty eff_f ->
      RegularResolvedKontShape heap k ty_res ty_out ->
      RegularResolvedKontShape heap
        (KCond et ef env rho k)
        TyBool
        ty_out
| RRKS_Ref :
    forall heap r ty k ty_out,
      RegularResolvedKontShape heap k
        (TyRef (region_const_type r) ty)
        ty_out ->
      RegularResolvedKontShape heap (KRef r k) ty ty_out
| RRKS_Deref :
    forall heap rgn r ty k ty_out,
      RegularResolvedKontShape heap k ty ty_out ->
      RegularResolvedKontShape heap (KDeref rgn k)
        (TyRef (region_const_type r) ty) ty_out
| RRKS_AssignLoc :
    forall heap rgn ev env rho k gamma omega r ty ty_res eff_v ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      eval_region rho rgn = Some r ->
      ResolveTy rho ty ty_res ->
      CheckedTcExp gamma omega ev ty eff_v ->
      RegularResolvedKontShape heap k TyUnit ty_out ->
      RegularResolvedKontShape heap
        (KAssignLoc rgn ev env rho k)
        (TyRef (region_const_type r) ty_res)
        ty_out
| RRKS_AssignVal :
    forall heap rgn r ty loc k ty_out,
      RegularResolvedValShape heap loc
        (TyRef (region_const_type r) ty) ->
      RegularResolvedKontShape heap k TyUnit ty_out ->
      RegularResolvedKontShape heap
        (KAssignVal rgn loc k)
        ty
        ty_out
| RRKS_PlusL :
    forall heap e2 env rho k gamma omega eff ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      CheckedTcExp gamma omega e2 TyNat eff ->
      RegularResolvedKontShape heap k TyNat ty_out ->
      RegularResolvedKontShape heap
        (KPlusL e2 env rho k)
        TyNat
        ty_out
| RRKS_PlusR :
    forall heap n k ty_out,
      RegularResolvedKontShape heap k TyNat ty_out ->
      RegularResolvedKontShape heap (KPlusR n k) TyNat ty_out
| RRKS_MinusL :
    forall heap e2 env rho k gamma omega eff ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      CheckedTcExp gamma omega e2 TyNat eff ->
      RegularResolvedKontShape heap k TyNat ty_out ->
      RegularResolvedKontShape heap
        (KMinusL e2 env rho k)
        TyNat
        ty_out
| RRKS_MinusR :
    forall heap n k ty_out,
      RegularResolvedKontShape heap k TyNat ty_out ->
      RegularResolvedKontShape heap (KMinusR n k) TyNat ty_out
| RRKS_TimesL :
    forall heap e2 env rho k gamma omega eff ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      CheckedTcExp gamma omega e2 TyNat eff ->
      RegularResolvedKontShape heap k TyNat ty_out ->
      RegularResolvedKontShape heap
        (KTimesL e2 env rho k)
        TyNat
        ty_out
| RRKS_TimesR :
    forall heap n k ty_out,
      RegularResolvedKontShape heap k TyNat ty_out ->
      RegularResolvedKontShape heap (KTimesR n k) TyNat ty_out
| RRKS_EqL :
    forall heap e2 env rho k gamma omega eff ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      CheckedTcExp gamma omega e2 TyNat eff ->
      RegularResolvedKontShape heap k TyBool ty_out ->
      RegularResolvedKontShape heap
        (KEqL e2 env rho k)
        TyNat
        ty_out
| RRKS_EqR :
    forall heap n k ty_out,
      RegularResolvedKontShape heap k TyBool ty_out ->
      RegularResolvedKontShape heap (KEqR n k) TyNat ty_out
| RRKS_ReadConc :
    forall heap k r ty ty_out,
      RegularResolvedKontShape heap k TyEffect ty_out ->
      RegularResolvedKontShape heap
        (KReadConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| RRKS_WriteConc :
    forall heap k r ty ty_out,
      RegularResolvedKontShape heap k TyEffect ty_out ->
      RegularResolvedKontShape heap
        (KWriteConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| RRKS_ConcatL :
    forall heap e2 env rho k gamma omega eff ty_out,
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      CheckedTcExp gamma omega e2 TyEffect eff ->
      RegularResolvedKontShape heap k TyEffect ty_out ->
      RegularResolvedKontShape heap
        (KConcatL e2 env rho k)
        TyEffect
        ty_out
| RRKS_ConcatR :
    forall heap theta k ty_out,
      RegularResolvedKontShape heap k TyEffect ty_out ->
      RegularResolvedKontShape heap
        (KConcatR theta k)
        TyEffect
        ty_out.

Inductive RegularResolvedStateShape : State -> Ty -> Prop :=
| RRSS_Eval :
    forall heap env rho e k gamma omega ty ty_res eff ty_out,
      RegularResolvedHeapShape heap ->
      RegularResolvedEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty ty_res ->
      CheckedTcExp gamma omega e ty eff ->
      RegularResolvedKontShape heap k ty_res ty_out ->
      RegularResolvedStateShape (StEval heap env rho e k) ty_out
| RRSS_Return :
    forall heap v k ty ty_out,
      RegularResolvedHeapShape heap ->
      RegularResolvedValShape heap v ty ->
      RegularResolvedKontShape heap k ty ty_out ->
      RegularResolvedStateShape (StReturn heap v k) ty_out
| RRSS_Done :
    forall heap v ty,
      RegularResolvedHeapShape heap ->
      RegularResolvedValShape heap v ty ->
      RegularResolvedStateShape (StDone heap v) ty
| RRSS_Error :
    forall heap ty,
      RegularResolvedHeapShape heap ->
      RegularResolvedStateShape (StError heap) ty
| RRSS_PairParRun :
    forall left_state right_state phi_left phi_right k
      heap ty1 ty2 ty_out,
      state_heap left_state = heap ->
      state_heap right_state = heap ->
      RegularResolvedStateShape left_state ty1 ->
      RegularResolvedStateShape right_state ty2 ->
      RegularResolvedKontShape heap k (TyPair ty1 ty2) ty_out ->
      RegularResolvedStateShape
        (StPairParRun left_state right_state phi_left phi_right k)
        ty_out.

Lemma RegularResolvedValShape_to_resolved :
  forall heap v ty,
    RegularResolvedValShape heap v ty ->
    ResolvedValShape heap v ty
with RegularResolvedEnvShape_to_resolved :
  forall rho heap env gamma,
    RegularResolvedEnvShape rho heap env gamma ->
    ResolvedEnvShape rho heap env gamma.
Proof.
  - intros heap v ty HVal.
    induction HVal.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + eapply RVS_Pair; eauto.
    + eapply RVS_Loc; eauto.
    + eapply RVS_Closure; eauto using CheckedTcExp_to_TcExp.
    + eapply RVS_RegionClosure; eauto.
      eapply CheckedRegionBody_to_TcExp; eauto.
  - intros rho heap env gamma HEnv.
    induction HEnv.
    + constructor.
    + econstructor; eauto.
Qed.

Lemma RegularResolvedHeapShape_to_resolved :
  forall heap,
    RegularResolvedHeapShape heap ->
    ResolvedHeapShape heap.
Proof.
  unfold RegularResolvedHeapShape, ResolvedHeapShape.
  intros heap HHeap r l v HLookup.
  destruct (HHeap r l v HLookup) as (ty & HVal).
  exists ty.
  eapply RegularResolvedValShape_to_resolved; eauto.
Qed.

Lemma RegularResolvedKontShape_to_resolved :
  forall heap k ty_in ty_out,
    RegularResolvedKontShape heap k ty_in ty_out ->
    ResolvedKontShape heap k ty_in ty_out.
Proof.
  intros heap k ty_in ty_out HK.
  induction HK.
  - constructor.
  - eapply RKS_MuAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_MuAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_EffAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_EffAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_PairParEff1 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2)
      (eff_summary2 := eff_summary2);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_PairParEff2 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_PairParFallbackLeft with
      (gamma := gamma) (omega := omega)
      (ty2 := ty2) (eff2 := eff2);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_PairParFallbackRight; eauto using
      RegularResolvedValShape_to_resolved.
  - eapply RKS_RgnApp; eauto.
  - eapply RKS_Cond with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_t := eff_t) (eff_f := eff_f);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_Ref; eauto.
  - eapply RKS_Deref; eauto.
  - eapply RKS_AssignLoc with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_v := eff_v);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_AssignVal; eauto using
      RegularResolvedValShape_to_resolved.
  - eapply RKS_PlusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_PlusR; eauto.
  - eapply RKS_MinusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_MinusR; eauto.
  - eapply RKS_TimesL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_TimesR; eauto.
  - eapply RKS_EqL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_EqR; eauto.
  - eapply RKS_ReadConc; eauto.
  - eapply RKS_WriteConc; eauto.
  - eapply RKS_ConcatL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using
        RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp.
  - eapply RKS_ConcatR; eauto.
Qed.

Lemma RegularResolvedStateShape_to_resolved :
  forall state ty,
    RegularResolvedStateShape state ty ->
    ResolvedStateShape state ty.
Proof.
  intros state ty HState.
  induction HState.
  - eapply RSS_Eval; eauto using
      RegularResolvedHeapShape_to_resolved,
      RegularResolvedEnvShape_to_resolved,
        CheckedTcExp_to_TcExp,
      RegularResolvedKontShape_to_resolved.
  - eapply RSS_Return; eauto using
      RegularResolvedHeapShape_to_resolved,
      RegularResolvedValShape_to_resolved,
      RegularResolvedKontShape_to_resolved.
  - eapply RSS_Done; eauto using
      RegularResolvedHeapShape_to_resolved,
      RegularResolvedValShape_to_resolved.
  - eapply RSS_Error; eauto using
      RegularResolvedHeapShape_to_resolved.
  - eapply RSS_PairParRun; eauto using
      RegularResolvedKontShape_to_resolved.
Qed.

Lemma RegularResolvedStateShape_initial :
  forall heap env rho e gamma omega ty ty_res eff,
    RegularResolvedHeapShape heap ->
    RegularResolvedEnvShape rho heap env gamma ->
    RhoModels omega rho ->
    ResolveTy rho ty ty_res ->
    CheckedTcExp gamma omega e ty eff ->
    RegularResolvedStateShape (InitialState heap env rho e) ty_res.
Proof.
  intros heap env rho e gamma omega ty ty_res eff
    HHeap HEnv HRho HResolve HTyped.
  unfold InitialState.
  eapply RRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty) (eff := eff);
    eauto.
  constructor.
Qed.

Corollary RegularResolvedStateShape_initial_effect :
  forall heap env rho e gamma omega eff,
    RegularResolvedHeapShape heap ->
    RegularResolvedEnvShape rho heap env gamma ->
    RhoModels omega rho ->
    CheckedTcExp gamma omega e TyEffect eff ->
    RegularResolvedStateShape (InitialState heap env rho e) TyEffect.
Proof.
  intros heap env rho e gamma omega eff HHeap HEnv HRho HTyped.
  eapply RegularResolvedStateShape_initial; eauto using Resolve_Effect.
Qed.

Lemma CheckedResolvedStateShape_initial :
  forall heap env rho e gamma omega ty ty_res eff,
    RegularResolvedHeapShape heap ->
    RegularResolvedEnvShape rho heap env gamma ->
    RhoModels omega rho ->
    ResolveTy rho ty ty_res ->
    CheckedTcExp gamma omega e ty eff ->
    RegularResolvedStateShape (InitialState heap env rho e) ty_res.
Proof.
  intros heap env rho e gamma omega ty ty_res eff
    HHeap HEnv HRho HResolve HChecked.
  eapply RegularResolvedStateShape_initial; eauto.
Qed.

Corollary CheckedResolvedStateShape_initial_effect :
  forall heap env rho e gamma omega eff,
    RegularResolvedHeapShape heap ->
    RegularResolvedEnvShape rho heap env gamma ->
    RhoModels omega rho ->
    CheckedTcExp gamma omega e TyEffect eff ->
    RegularResolvedStateShape (InitialState heap env rho e) TyEffect.
Proof.
  intros heap env rho e gamma omega eff HHeap HEnv HRho HChecked.
  eapply CheckedResolvedStateShape_initial; eauto using Resolve_Effect.
Qed.

Lemma RegularResolvedStateShape_aligned :
  forall state ty,
    RegularResolvedStateShape state ty ->
    StateHeapsAligned state.
Proof.
  intros state ty HState.
  induction HState; simpl; try exact I.
  repeat split; assumption || congruence.
Qed.

Definition StoreTyping := list (RegionId * Location * Ty).

Fixpoint store_ty_lookup
    (r : RegionId) (l : Location)
    (store : StoreTyping) : option Ty :=
  match store with
  | [] => None
  | (r', l', ty) :: store' =>
      if Nat.eqb r r' && Nat.eqb l l'
      then Some ty
      else store_ty_lookup r l store'
  end.

Definition StoreKeysBoundedByHeap
    (heap : Heap) (store : StoreTyping) : Prop :=
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
    StoreKeysBoundedByHeap heap store ->
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

Inductive StoreResolvedValShape : StoreTyping -> Val -> Ty -> Prop :=
| SRVS_Nat :
    forall store n,
      StoreResolvedValShape store (VNat n) TyNat
| SRVS_Bool :
    forall store b,
      StoreResolvedValShape store (VBool b) TyBool
| SRVS_Unit :
    forall store,
      StoreResolvedValShape store VUnit TyUnit
| SRVS_Summary :
    forall store theta,
      StoreResolvedValShape store (VSummary theta) TyEffect
| SRVS_Pair :
    forall store v1 v2 ty1 ty2,
      StoreResolvedValShape store v1 ty1 ->
      StoreResolvedValShape store v2 ty2 ->
      StoreResolvedValShape store (VPair v1 v2) (TyPair ty1 ty2)
| SRVS_Loc :
    forall store r l ty,
      store_ty_lookup r l store = Some ty ->
      StoreResolvedValShape store
        (VLoc r l)
        (TyRef (region_const_type r) ty)
| SRVS_Closure :
    forall store closure_env closure_rho f x ec ee
      gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      StoreResolvedEnvShape store closure_rho closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveTy closure_rho ty_arg ty_arg_res ->
      ResolveStaticEffect closure_rho eff_body eff_body_res ->
      ResolveTy closure_rho ty_body ty_body_res ->
      ResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      CheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      StoreResolvedValShape store
        (VClosure closure_env closure_rho f x ec ee)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
| SRVS_RegionClosure :
    forall store closure_env closure_rho x e gamma omega ty ty_res eff eff_res,
      StoreResolvedEnvShape store closure_rho closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveStaticEffect closure_rho (close_static_effect x eff) eff_res ->
      ResolveTy closure_rho (close_ty x ty) ty_res ->
      CheckedRegionBody x gamma omega e ty eff ->
      StoreResolvedValShape store
        (VRegionClosure closure_env closure_rho x e)
        (TyForallRgn eff_res ty_res)
with StoreResolvedEnvShape : StoreTyping -> Rho -> Env -> Ctx -> Prop :=
| SRES_EnvNil :
    forall store rho,
      StoreResolvedEnvShape store rho EnvNil []
| SRES_EnvCons :
    forall store rho x v env ty ty_res gamma,
      ResolveTy rho ty ty_res ->
      StoreResolvedValShape store v ty_res ->
      StoreResolvedEnvShape store rho env gamma ->
      StoreResolvedEnvShape store rho (EnvCons x v env) ((x, ty) :: gamma).

Scheme StoreResolvedValShape_ind' :=
  Induction for StoreResolvedValShape Sort Prop
with StoreResolvedEnvShape_ind' :=
  Induction for StoreResolvedEnvShape Sort Prop.

Combined Scheme StoreResolvedValShape_StoreResolvedEnvShape_ind
  from StoreResolvedValShape_ind', StoreResolvedEnvShape_ind'.

Lemma StoreResolvedEnvShape_lookup :
  forall store rho env gamma x ty ty_res,
    StoreResolvedEnvShape store rho env gamma ->
    ctx_binds x ty gamma ->
    ResolveTy rho ty ty_res ->
    exists v,
      env_lookup x env = Some v /\
      StoreResolvedValShape store v ty_res.
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
      | HStored : ResolveTy rho ?ty ?ty_stored,
        HGoal : ResolveTy rho ?ty ?ty_goal,
        HVStored : StoreResolvedValShape store v ?ty_stored |- _ =>
          pose proof
            (ResolveTy_deterministic
              rho ty ty_stored ty_goal HStored HGoal)
            as HResolvedEq;
          subst ty_goal;
          exists v; split; [reflexivity | exact HVStored]
      end.
    + apply IH; assumption.
Qed.

Lemma StoreResolvedEnvShape_extend :
  forall store rho env gamma x v ty ty_res,
    ResolveTy rho ty ty_res ->
    StoreResolvedValShape store v ty_res ->
    StoreResolvedEnvShape store rho env gamma ->
    StoreResolvedEnvShape store rho
      (env_extend x v env)
      ((x, ty) :: gamma).
Proof.
  intros store rho env gamma x v ty ty_res HResolve HVal HEnv.
  eapply SRES_EnvCons; eauto.
Qed.

Lemma StoreResolvedEnvShape_extend_fresh :
  forall store rho env gamma omega x r_val,
    ~ In x omega ->
    CtxWF omega gamma ->
    StoreResolvedEnvShape store rho env gamma ->
    StoreResolvedEnvShape store (rho_extend x r_val rho) env gamma.
Proof.
  intros store rho env gamma omega x r_val HFresh HCtxWF HEnv.
  induction HEnv as
    [store rho
    | store rho y v env ty ty_res gamma HResolve HV HEnv IH].
  - constructor.
  - inversion HCtxWF as [| binding gamma_tail HBindingWF HCtxTailWF];
      subst; simpl in HBindingWF.
    econstructor; eauto.
    eapply ResolveTy_extend_fresh; eauto.
Qed.

Definition StoreResolvedHeapShape
    (heap : Heap) (store : StoreTyping) : Prop :=
  (forall r l v,
    heap_lookup r l heap = Some v ->
    exists ty,
      store_ty_lookup r l store = Some ty /\
      StoreResolvedValShape store v ty) /\
  (forall r l ty,
    store_ty_lookup r l store = Some ty ->
    exists v,
      heap_lookup r l heap = Some v /\
      StoreResolvedValShape store v ty).

Definition StoreResolvedRuntimeShape
    (heap : Heap) (store : StoreTyping)
    (env : Env) (rho : Rho) (gamma : Ctx) : Prop :=
  StoreKeysBoundedByHeap heap store /\
  StoreResolvedHeapShape heap store /\
  StoreResolvedEnvShape store rho env gamma.

Inductive StoreResolvedKontShape :
    StoreTyping -> Kont -> Ty -> Ty -> Prop :=
| SRKS_Done :
    forall store ty,
      StoreResolvedKontShape store KDone ty ty
| SRKS_MuAppFun :
    forall store ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty_arg ty_arg_res ->
      ResolveStaticEffect rho eff_body eff_body_res ->
      ResolveTy rho ty_body ty_body_res ->
      ResolveStaticEffect rho eff_summary eff_summary_res ->
      CheckedTcExp gamma omega ea ty_arg eff_arg ->
      StoreResolvedKontShape store k ty_body_res ty_out ->
      StoreResolvedKontShape store
        (KMuAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| SRKS_MuAppArg :
    forall store closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      StoreResolvedEnvShape store closure_rho closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveTy closure_rho ty_arg ty_arg_res ->
      ResolveStaticEffect closure_rho eff_body eff_body_res ->
      ResolveTy closure_rho ty_body ty_body_res ->
      ResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      CheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      StoreResolvedKontShape store k ty_body_res ty_out ->
      StoreResolvedKontShape store
        (KMuAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| SRKS_EffAppFun :
    forall store ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res eff_arg ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty_arg ty_arg_res ->
      ResolveStaticEffect rho eff_body eff_body_res ->
      ResolveTy rho ty_body ty_body_res ->
      ResolveStaticEffect rho eff_summary eff_summary_res ->
      CheckedTcExp gamma omega ea ty_arg eff_arg ->
      StoreResolvedKontShape store k TyEffect ty_out ->
      StoreResolvedKontShape store
        (KEffAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| SRKS_EffAppArg :
    forall store closure_env closure_rho f x ec ee k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res ty_out,
      StoreResolvedEnvShape store closure_rho closure_env gamma ->
      RhoModels omega closure_rho ->
      ResolveTy closure_rho ty_arg ty_arg_res ->
      ResolveStaticEffect closure_rho eff_body eff_body_res ->
      ResolveTy closure_rho ty_body ty_body_res ->
      ResolveStaticEffect closure_rho eff_summary eff_summary_res ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      CheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee ->
      StoreResolvedKontShape store k TyEffect ty_out ->
      StoreResolvedKontShape store
        (KEffAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| SRKS_PairParEff1 :
    forall store ef1 ea1 ef2 ea2 env rho k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 eff_summary2 ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty1 ty1_res ->
      ResolveTy rho ty2 ty2_res ->
      CheckedTcExp gamma omega
        (EMuApp ef1 ea1) ty1 eff1 ->
      CheckedTcExp gamma omega
        (EMuApp ef2 ea2) ty2 eff2 ->
      CheckedTcExp gamma omega
        (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      StoreResolvedKontShape store k (TyPair ty1_res ty2_res) ty_out ->
      StoreResolvedKontShape store
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
        TyEffect
        ty_out
| SRKS_PairParEff2 :
    forall store ef1 ea1 ef2 ea2 env rho theta1 k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff2 ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty1 ty1_res ->
      ResolveTy rho ty2 ty2_res ->
      CheckedTcExp gamma omega
        (EMuApp ef1 ea1) ty1 eff1 ->
      CheckedTcExp gamma omega
        (EMuApp ef2 ea2) ty2 eff2 ->
      StoreResolvedKontShape store k (TyPair ty1_res ty2_res) ty_out ->
      StoreResolvedKontShape store
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
        TyEffect
        ty_out
| SRKS_PairParFallbackLeft :
    forall store ef2 ea2 env rho k gamma omega
      ty_left_res ty2 ty2_res eff2 ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty2 ty2_res ->
      CheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      StoreResolvedKontShape store k
        (TyPair ty_left_res ty2_res) ty_out ->
      StoreResolvedKontShape store
        (KPairParFallbackLeft ef2 ea2 env rho k)
        ty_left_res
        ty_out
| SRKS_PairParFallbackRight :
    forall store v_left k ty_left_res ty2_res ty_out,
      StoreResolvedValShape store v_left ty_left_res ->
      StoreResolvedKontShape store k
        (TyPair ty_left_res ty2_res) ty_out ->
      StoreResolvedKontShape store
        (KPairParFallbackRight v_left k)
        ty2_res
        ty_out
| SRKS_RgnApp :
    forall store r arg_rho r_val k eff ty ty_out,
      eval_region arg_rho r = Some r_val ->
      StoreResolvedKontShape store k
        (open_ty_type (region_const_type r_val) ty)
        ty_out ->
      StoreResolvedKontShape store
        (KRgnApp r arg_rho k)
        (TyForallRgn eff ty)
        ty_out
| SRKS_Cond :
    forall store et ef env rho k gamma omega ty ty_res eff_t eff_f ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty ty_res ->
      CheckedTcExp gamma omega et ty eff_t ->
      CheckedTcExp gamma omega ef ty eff_f ->
      StoreResolvedKontShape store k ty_res ty_out ->
      StoreResolvedKontShape store
        (KCond et ef env rho k)
        TyBool
        ty_out
| SRKS_Ref :
    forall store r ty k ty_out,
      StoreResolvedKontShape store k
        (TyRef (region_const_type r) ty)
        ty_out ->
      StoreResolvedKontShape store (KRef r k) ty ty_out
| SRKS_Deref :
    forall store rgn r ty k ty_out,
      StoreResolvedKontShape store k ty ty_out ->
      StoreResolvedKontShape store (KDeref rgn k)
        (TyRef (region_const_type r) ty) ty_out
| SRKS_AssignLoc :
    forall store rgn ev env rho k gamma omega r ty ty_res eff_v ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      eval_region rho rgn = Some r ->
      ResolveTy rho ty ty_res ->
      CheckedTcExp gamma omega ev ty eff_v ->
      StoreResolvedKontShape store k TyUnit ty_out ->
      StoreResolvedKontShape store
        (KAssignLoc rgn ev env rho k)
        (TyRef (region_const_type r) ty_res)
        ty_out
| SRKS_AssignVal :
    forall store rgn r ty loc k ty_out,
      StoreResolvedValShape store loc
        (TyRef (region_const_type r) ty) ->
      StoreResolvedKontShape store k TyUnit ty_out ->
      StoreResolvedKontShape store
        (KAssignVal rgn loc k)
        ty
        ty_out
| SRKS_PlusL :
    forall store e2 env rho k gamma omega eff ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      CheckedTcExp gamma omega e2 TyNat eff ->
      StoreResolvedKontShape store k TyNat ty_out ->
      StoreResolvedKontShape store
        (KPlusL e2 env rho k)
        TyNat
        ty_out
| SRKS_PlusR :
    forall store n k ty_out,
      StoreResolvedKontShape store k TyNat ty_out ->
      StoreResolvedKontShape store (KPlusR n k) TyNat ty_out
| SRKS_MinusL :
    forall store e2 env rho k gamma omega eff ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      CheckedTcExp gamma omega e2 TyNat eff ->
      StoreResolvedKontShape store k TyNat ty_out ->
      StoreResolvedKontShape store
        (KMinusL e2 env rho k)
        TyNat
        ty_out
| SRKS_MinusR :
    forall store n k ty_out,
      StoreResolvedKontShape store k TyNat ty_out ->
      StoreResolvedKontShape store (KMinusR n k) TyNat ty_out
| SRKS_TimesL :
    forall store e2 env rho k gamma omega eff ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      CheckedTcExp gamma omega e2 TyNat eff ->
      StoreResolvedKontShape store k TyNat ty_out ->
      StoreResolvedKontShape store
        (KTimesL e2 env rho k)
        TyNat
        ty_out
| SRKS_TimesR :
    forall store n k ty_out,
      StoreResolvedKontShape store k TyNat ty_out ->
      StoreResolvedKontShape store (KTimesR n k) TyNat ty_out
| SRKS_EqL :
    forall store e2 env rho k gamma omega eff ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      CheckedTcExp gamma omega e2 TyNat eff ->
      StoreResolvedKontShape store k TyBool ty_out ->
      StoreResolvedKontShape store
        (KEqL e2 env rho k)
        TyNat
        ty_out
| SRKS_EqR :
    forall store n k ty_out,
      StoreResolvedKontShape store k TyBool ty_out ->
      StoreResolvedKontShape store (KEqR n k) TyNat ty_out
| SRKS_ReadConc :
    forall store k r ty ty_out,
      StoreResolvedKontShape store k TyEffect ty_out ->
      StoreResolvedKontShape store
        (KReadConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| SRKS_WriteConc :
    forall store k r ty ty_out,
      StoreResolvedKontShape store k TyEffect ty_out ->
      StoreResolvedKontShape store
        (KWriteConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| SRKS_ConcatL :
    forall store e2 env rho k gamma omega eff ty_out,
      StoreResolvedEnvShape store rho env gamma ->
      RhoModels omega rho ->
      CheckedTcExp gamma omega e2 TyEffect eff ->
      StoreResolvedKontShape store k TyEffect ty_out ->
      StoreResolvedKontShape store
        (KConcatL e2 env rho k)
        TyEffect
        ty_out
| SRKS_ConcatR :
    forall store theta k ty_out,
      StoreResolvedKontShape store k TyEffect ty_out ->
      StoreResolvedKontShape store
        (KConcatR theta k)
        TyEffect
        ty_out.

Inductive StoreResolvedStateShape :
    StoreTyping -> State -> Ty -> Prop :=
| SRSS_Eval :
    forall store heap env rho e k gamma omega ty ty_res eff ty_out,
      StoreResolvedRuntimeShape heap store env rho gamma ->
      RhoModels omega rho ->
      ResolveTy rho ty ty_res ->
      CheckedTcExp gamma omega e ty eff ->
      StoreResolvedKontShape store k ty_res ty_out ->
      StoreResolvedStateShape store (StEval heap env rho e k) ty_out
| SRSS_Return :
    forall store heap v k ty ty_out,
      StoreKeysBoundedByHeap heap store ->
      StoreResolvedHeapShape heap store ->
      StoreResolvedValShape store v ty ->
      StoreResolvedKontShape store k ty ty_out ->
      StoreResolvedStateShape store (StReturn heap v k) ty_out
| SRSS_Done :
    forall store heap v ty,
      StoreKeysBoundedByHeap heap store ->
      StoreResolvedHeapShape heap store ->
      StoreResolvedValShape store v ty ->
      StoreResolvedStateShape store (StDone heap v) ty
| SRSS_Error :
    forall store heap ty,
      StoreKeysBoundedByHeap heap store ->
      StoreResolvedHeapShape heap store ->
      StoreResolvedStateShape store (StError heap) ty
| SRSS_PairParRun :
    forall store left_state right_state phi_left phi_right k
      heap ty1 ty2 ty_out,
      state_heap left_state = heap ->
      state_heap right_state = heap ->
      StoreResolvedStateShape store left_state ty1 ->
      StoreResolvedStateShape store right_state ty2 ->
      StoreResolvedKontShape store k (TyPair ty1 ty2) ty_out ->
      StoreResolvedStateShape store
        (StPairParRun left_state right_state phi_left phi_right k)
        ty_out.

Lemma StoreResolvedValShape_pair_inv :
  forall store v1 v2 ty,
    StoreResolvedValShape store (VPair v1 v2) ty ->
    exists ty1 ty2,
      ty = TyPair ty1 ty2 /\
      StoreResolvedValShape store v1 ty1 /\
      StoreResolvedValShape store v2 ty2.
Proof.
  intros store v1 v2 ty HVal.
  inversion HVal; subst.
  exists ty1, ty2.
  repeat split; assumption || reflexivity.
Qed.

Lemma StoreResolvedStateShape_done_inv :
  forall store heap v ty,
    StoreResolvedStateShape store (StDone heap v) ty ->
    StoreKeysBoundedByHeap heap store /\
    StoreResolvedHeapShape heap store /\
    StoreResolvedValShape store v ty.
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

Lemma StoreResolvedStateShape_done_summary_inv :
  forall store heap theta ty,
    StoreResolvedStateShape store (StDone heap (VSummary theta)) ty ->
    ty = TyEffect /\
    StoreKeysBoundedByHeap heap store /\
    StoreResolvedHeapShape heap store.
Proof.
  intros store heap theta ty HState.
  destruct
    (StoreResolvedStateShape_done_inv
      store heap (VSummary theta) ty HState)
    as (HBounded & HHeap & HVal).
  dependent destruction HVal.
  split; [reflexivity |].
  split; assumption.
Qed.

Lemma StoreResolvedStateShape_done_pair_inv :
  forall store heap v1 v2 ty,
    StoreResolvedStateShape store (StDone heap (VPair v1 v2)) ty ->
    exists ty1 ty2,
      ty = TyPair ty1 ty2 /\
      StoreKeysBoundedByHeap heap store /\
      StoreResolvedHeapShape heap store /\
      StoreResolvedValShape store v1 ty1 /\
      StoreResolvedValShape store v2 ty2.
Proof.
  intros store heap v1 v2 ty HState.
  destruct
    (StoreResolvedStateShape_done_inv
      store heap (VPair v1 v2) ty HState)
    as (HBounded & HHeap & HVal).
  destruct
    (StoreResolvedValShape_pair_inv store v1 v2 ty HVal)
    as (ty1 & ty2 & HTy & HVal1 & HVal2).
  exists ty1, ty2.
  split; [exact HTy |].
  split; [exact HBounded |].
  split; [exact HHeap |].
  split; assumption.
Qed.

Lemma StoreResolvedValShape_closure_inv :
  forall store closure_env closure_rho f x ec ee ty,
    StoreResolvedValShape store
      (VClosure closure_env closure_rho f x ec ee)
      ty ->
    exists gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      ty =
        TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res /\
      StoreResolvedEnvShape store closure_rho closure_env gamma /\
      RhoModels omega closure_rho /\
      ResolveTy closure_rho ty_arg ty_arg_res /\
      ResolveStaticEffect closure_rho eff_body eff_body_res /\
      ResolveTy closure_rho ty_body ty_body_res /\
      ResolveStaticEffect closure_rho eff_summary eff_summary_res /\
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body /\
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary /\
      CheckedBackTriangle
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

Lemma StoreResolvedValShape_region_closure_inv :
  forall store closure_env closure_rho x e ty_final,
    StoreResolvedValShape store
      (VRegionClosure closure_env closure_rho x e)
      ty_final ->
    exists gamma omega ty_body ty_res eff eff_res,
      ty_final = TyForallRgn eff_res ty_res /\
      StoreResolvedEnvShape store closure_rho closure_env gamma /\
      RhoModels omega closure_rho /\
      ResolveStaticEffect closure_rho
        (close_static_effect x eff) eff_res /\
      ResolveTy closure_rho (close_ty x ty_body) ty_res /\
      CheckedRegionBody x gamma omega e ty_body eff.
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

Lemma StoreResolvedStateShape_done_closure_inv :
  forall store heap closure_env closure_rho f x ec ee ty,
    StoreResolvedStateShape store
      (StDone heap (VClosure closure_env closure_rho f x ec ee))
      ty ->
    exists gamma omega ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res,
      StoreKeysBoundedByHeap heap store /\
      StoreResolvedHeapShape heap store /\
      ty =
        TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res /\
      StoreResolvedEnvShape store closure_rho closure_env gamma /\
      RhoModels omega closure_rho /\
      ResolveTy closure_rho ty_arg ty_arg_res /\
      ResolveStaticEffect closure_rho eff_body eff_body_res /\
      ResolveTy closure_rho ty_body ty_body_res /\
      ResolveStaticEffect closure_rho eff_summary eff_summary_res /\
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body /\
      CheckedTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary /\
      CheckedBackTriangle
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ee.
Proof.
  intros store heap closure_env closure_rho f x ec ee ty HState.
  destruct
    (StoreResolvedStateShape_done_inv
      store heap
      (VClosure closure_env closure_rho f x ec ee)
      ty
      HState)
    as (HBounded & HHeap & HVal).
  destruct
    (StoreResolvedValShape_closure_inv
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

Lemma StoreResolvedStateShape_aligned :
  forall store state ty,
    StoreResolvedStateShape store state ty ->
    StateHeapsAligned state.
Proof.
  intros store state ty HState.
  induction HState; simpl; try exact I.
  repeat split; assumption || congruence.
Qed.

Lemma StoreResolvedStateShape_with_state_heap_same :
  forall store state ty heap,
    StoreResolvedStateShape store state ty ->
    state_heap state = heap ->
    StoreResolvedStateShape store (with_state_heap heap state) ty.
Proof.
  intros store state ty heap HState HHeap.
  rewrite (with_state_heap_aligned_same heap state).
  - exact HState.
  - eapply StoreResolvedStateShape_aligned; eauto.
  - exact HHeap.
Qed.

Lemma StoreResolvedStateShape_initial :
  forall heap store env rho e gamma omega ty ty_res eff,
    StoreResolvedRuntimeShape heap store env rho gamma ->
    RhoModels omega rho ->
    ResolveTy rho ty ty_res ->
    CheckedTcExp gamma omega e ty eff ->
    StoreResolvedStateShape store (InitialState heap env rho e) ty_res.
Proof.
  intros heap store env rho e gamma omega ty ty_res eff
    HRuntime HRho HResolve HChecked.
  unfold InitialState.
  eapply SRSS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty) (eff := eff);
    eauto.
  constructor.
Qed.

Lemma StoreKeysBoundedByHeap_update :
  forall heap store r l v,
    StoreKeysBoundedByHeap heap store ->
    StoreKeysBoundedByHeap (heap_update r l v heap) store.
Proof.
  intros heap store r l v HBounded r' l' ty HIn.
  rewrite heap_update_length.
  eapply HBounded; eauto.
Qed.

Lemma StoreResolvedHeapShape_update :
  forall heap store r l old v ty,
    StoreResolvedHeapShape heap store ->
    heap_lookup r l heap = Some old ->
    store_ty_lookup r l store = Some ty ->
    StoreResolvedValShape store v ty ->
    StoreResolvedHeapShape (heap_update r l v heap) store.
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

Lemma StoreResolvedRuntimeShape_update :
  forall heap store env rho gamma r l old v ty,
    StoreResolvedRuntimeShape heap store env rho gamma ->
    heap_lookup r l heap = Some old ->
    store_ty_lookup r l store = Some ty ->
    StoreResolvedValShape store v ty ->
    StoreResolvedRuntimeShape
      (heap_update r l v heap)
      store env rho gamma.
Proof.
  intros heap store env rho gamma r l old v ty
    (HBounded & HHeap & HEnv) HOldLookup HStoreLookup HVal.
  split.
  - eapply StoreKeysBoundedByHeap_update; eauto.
  - split.
    + eapply StoreResolvedHeapShape_update; eauto.
    + exact HEnv.
Qed.

Lemma StoreResolvedValShape_store_extend :
  forall heap store r_new l_new ty_new v ty,
    StoreKeysBoundedByHeap heap store ->
    l_new = length heap ->
    StoreResolvedValShape store v ty ->
    StoreResolvedValShape ((r_new, l_new, ty_new) :: store) v ty
with StoreResolvedEnvShape_store_extend :
  forall heap store r_new l_new ty_new rho env gamma,
    StoreKeysBoundedByHeap heap store ->
    l_new = length heap ->
    StoreResolvedEnvShape store rho env gamma ->
    StoreResolvedEnvShape ((r_new, l_new, ty_new) :: store) rho env gamma.
Proof.
  - intros heap store r_new l_new ty_new v ty
      HBounded HFresh HVal.
    induction HVal.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + eapply SRVS_Pair; eauto.
    + eapply SRVS_Loc.
      eapply store_ty_lookup_extend_old; eauto.
    + eapply SRVS_Closure with
        (gamma := gamma) (omega := omega)
        (ty_arg := ty_arg) (ty_body := ty_body);
        eauto.
    + eapply SRVS_RegionClosure with
        (gamma := gamma) (omega := omega);
        eauto.
  - intros heap store r_new l_new ty_new rho env gamma
      HBounded HFresh HEnv.
    induction HEnv.
    + constructor.
    + econstructor; eauto.
Qed.

Lemma StoreResolvedKontShape_store_extend :
  forall heap store r_new l_new ty_new k ty_in ty_out,
    StoreKeysBoundedByHeap heap store ->
    l_new = length heap ->
    StoreResolvedKontShape store k ty_in ty_out ->
    StoreResolvedKontShape
      ((r_new, l_new, ty_new) :: store) k ty_in ty_out.
Proof.
  intros heap store r_new l_new ty_new k ty_in ty_out
    HBounded HFresh HK.
  induction HK; try solve [econstructor; eauto].
  - eapply SRKS_MuAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_MuAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_EffAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_EffAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_PairParEff1 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2)
      (eff_summary2 := eff_summary2);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_PairParEff2 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_PairParFallbackLeft with
      (gamma := gamma) (omega := omega)
      (ty2 := ty2) (eff2 := eff2);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_PairParFallbackRight; eauto.
    eapply StoreResolvedValShape_store_extend; eauto.
  - eapply SRKS_Cond with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_t := eff_t) (eff_f := eff_f);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_AssignLoc with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_v := eff_v);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_AssignVal; eauto.
    eapply StoreResolvedValShape_store_extend; eauto.
  - eapply SRKS_PlusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_MinusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_TimesL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_EqL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using StoreResolvedEnvShape_store_extend.
  - eapply SRKS_ConcatL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using StoreResolvedEnvShape_store_extend.
Qed.

Lemma StoreKeysBoundedByHeap_alloc :
  forall heap store r_new l_new v_new ty_new heap',
    StoreKeysBoundedByHeap heap store ->
    heap_alloc r_new v_new heap = (l_new, heap') ->
    StoreKeysBoundedByHeap
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

Lemma StoreResolvedHeapShape_alloc :
  forall heap store r_new v_new ty_new l_new heap',
    StoreKeysBoundedByHeap heap store ->
    StoreResolvedHeapShape heap store ->
    StoreResolvedValShape store v_new ty_new ->
    heap_alloc r_new v_new heap = (l_new, heap') ->
    StoreResolvedHeapShape
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
      * eapply StoreResolvedValShape_store_extend; eauto.
    + destruct (HHeapToStore r l v HLookup) as
        (ty & HStoreLookup & HShape).
      exists ty.
      split.
      * eapply store_ty_lookup_extend_old; eauto.
      * eapply StoreResolvedValShape_store_extend; eauto.
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
      * eapply StoreResolvedValShape_store_extend; eauto.
    + destruct (HStoreToHeap r l ty HStoreLookup) as
        (v & HHeapLookup & HShape).
      exists v.
      split.
      * simpl. rewrite HEq. exact HHeapLookup.
      * eapply StoreResolvedValShape_store_extend; eauto.
Qed.

Lemma StoreResolvedRuntimeShape_alloc :
  forall heap store env rho gamma r_new v_new ty_new l_new heap',
    StoreResolvedRuntimeShape heap store env rho gamma ->
    StoreResolvedValShape store v_new ty_new ->
    heap_alloc r_new v_new heap = (l_new, heap') ->
    StoreResolvedRuntimeShape
      heap' ((r_new, l_new, ty_new) :: store) env rho gamma.
Proof.
  intros heap store env rho gamma r_new v_new ty_new l_new heap'
    (HBounded & HHeap & HEnv) HValNew HAlloc.
  split.
  - eapply StoreKeysBoundedByHeap_alloc; eauto.
  - split.
    + eapply StoreResolvedHeapShape_alloc; eauto.
    + destruct (heap_alloc_result heap r_new v_new l_new heap')
        as [HFresh _]; [exact HAlloc |].
      eapply StoreResolvedEnvShape_store_extend; eauto.
Qed.

Lemma StoreResolvedStateShape_heap_update :
  forall state store ty heap r l old v ty_cell,
    state_heap state = heap ->
    heap_lookup r l heap = Some old ->
    store_ty_lookup r l store = Some ty_cell ->
    StoreResolvedValShape store v ty_cell ->
    StoreResolvedStateShape store state ty ->
    StoreResolvedStateShape store
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
    eapply SRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty) (eff := eff);
      eauto.
    eapply StoreResolvedRuntimeShape_update; eauto.
  - subst heap_current.
    simpl.
    eapply SRSS_Return with (ty := ty);
      eauto using
        StoreKeysBoundedByHeap_update,
        StoreResolvedHeapShape_update.
  - subst heap_current.
    simpl.
    eapply SRSS_Done with (ty := ty);
      eauto using
        StoreKeysBoundedByHeap_update,
        StoreResolvedHeapShape_update.
  - subst heap_current.
    simpl.
    eapply SRSS_Error;
      eauto using
        StoreKeysBoundedByHeap_update,
        StoreResolvedHeapShape_update.
  - simpl.
    pose proof
      (StoreResolvedStateShape_aligned _ _ _ HState1)
      as HAlignedLeft.
    pose proof
      (StoreResolvedStateShape_aligned _ _ _ HState2)
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
    eapply SRSS_PairParRun with
      (heap := heap_update r_update l_update v_update heap_current)
      (ty1 := ty1) (ty2 := ty2).
    + exact HLeftHeap'.
    + exact HRightHeap'.
    + eapply IHHState1; eauto.
    + eapply IHHState2; eauto.
    + eauto.
Qed.

Lemma StoreResolvedStateShape_heap_alloc :
  forall state store ty heap r_alloc v_alloc ty_alloc l_alloc heap',
    StoreKeysBoundedByHeap heap store ->
    state_heap state = heap ->
    StoreResolvedValShape store v_alloc ty_alloc ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    StoreResolvedStateShape store state ty ->
    StoreResolvedStateShape
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
    eapply SRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty) (eff := eff).
    + eapply StoreResolvedRuntimeShape_alloc; eauto.
    + eauto.
    + eauto.
    + eauto.
    + destruct (heap_alloc_result heap r_alloc v_alloc l_alloc heap')
        as [HFresh _]; [exact HAlloc |].
      eapply StoreResolvedKontShape_store_extend; eauto.
  - subst heap_current.
    simpl.
    eapply SRSS_Return with (ty := ty).
    + eapply StoreKeysBoundedByHeap_alloc; eauto.
    + eapply StoreResolvedHeapShape_alloc; eauto.
    + destruct (heap_alloc_result heap r_alloc v_alloc l_alloc heap')
        as [HFresh _]; [exact HAlloc |].
      eapply StoreResolvedValShape_store_extend; eauto.
    + destruct (heap_alloc_result heap r_alloc v_alloc l_alloc heap')
        as [HFresh _]; [exact HAlloc |].
      eapply StoreResolvedKontShape_store_extend; eauto.
  - subst heap_current.
    simpl.
    eapply SRSS_Done with (ty := ty).
    + eapply StoreKeysBoundedByHeap_alloc; eauto.
    + eapply StoreResolvedHeapShape_alloc; eauto.
    + destruct (heap_alloc_result heap r_alloc v_alloc l_alloc heap')
        as [HFresh _]; [exact HAlloc |].
      eapply StoreResolvedValShape_store_extend; eauto.
  - subst heap_current.
    simpl.
    eapply SRSS_Error.
    + eapply StoreKeysBoundedByHeap_alloc; eauto.
    + eapply StoreResolvedHeapShape_alloc; eauto.
  - simpl.
    pose proof
      (StoreResolvedStateShape_aligned _ _ _ HState1)
      as HAlignedLeft.
    pose proof
      (StoreResolvedStateShape_aligned _ _ _ HState2)
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
    eapply SRSS_PairParRun with
      (heap := heap') (ty1 := ty1) (ty2 := ty2).
    + exact HLeftHeap'.
    + exact HRightHeap'.
    + eapply IHHState1; eauto.
    + eapply IHHState2; eauto.
    + destruct (heap_alloc_result heap_current r_alloc v_alloc l_alloc heap')
        as [HFresh _]; [exact HAlloc |].
      eapply StoreResolvedKontShape_store_extend; eauto.
Qed.

Lemma RegularResolvedValShape_heap_alloc :
  forall heap r_alloc v_alloc l_alloc heap' v ty,
    HeapKeysBounded heap ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    RegularResolvedValShape heap v ty ->
    RegularResolvedValShape heap' v ty
with RegularResolvedEnvShape_heap_alloc :
  forall rho heap env gamma r_alloc v_alloc l_alloc heap',
    HeapKeysBounded heap ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    RegularResolvedEnvShape rho heap env gamma ->
    RegularResolvedEnvShape rho heap' env gamma.
Proof.
  - intros heap r_alloc v_alloc l_alloc heap' v ty
      HBounded HAlloc HVal.
    induction HVal.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + eapply RRVS_Pair; eauto.
    + eapply RRVS_Loc; eauto.
      eapply heap_lookup_alloc_old; eauto.
    + eapply RRVS_Closure with
        (gamma := gamma) (omega := omega)
        (ty_arg := ty_arg) (ty_body := ty_body);
        eauto.
    + eapply RRVS_RegionClosure with
        (gamma := gamma) (omega := omega);
        eauto.
  - intros rho heap env gamma r_alloc v_alloc l_alloc heap'
      HBounded HAlloc HEnv.
    induction HEnv.
    + constructor.
    + econstructor; eauto.
Qed.

Lemma RegularResolvedHeapShape_alloc :
  forall heap r_alloc v_alloc ty_alloc l_alloc heap',
    HeapKeysBounded heap ->
    RegularResolvedHeapShape heap ->
    RegularResolvedValShape heap v_alloc ty_alloc ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    RegularResolvedHeapShape heap'.
Proof.
  intros heap r_alloc v_alloc ty_alloc l_alloc heap'
    HBounded HHeap HAllocVal HAlloc.
  pose proof HAlloc as HAllocShape.
  destruct
    (heap_alloc_result heap r_alloc v_alloc l_alloc heap' HAlloc)
    as [-> ->].
  unfold RegularResolvedHeapShape in *.
  intros r l v HLookup.
  simpl in HLookup.
  destruct (Nat.eqb r r_alloc && Nat.eqb l (length heap)) eqn:HEq.
  - inversion HLookup; subst.
    exists ty_alloc.
    eapply RegularResolvedValShape_heap_alloc; eauto.
  - destruct (HHeap r l v HLookup) as (ty & HVal).
    exists ty.
    eapply RegularResolvedValShape_heap_alloc; eauto.
Qed.

Lemma RegularResolvedKontShape_heap_alloc :
  forall heap r_alloc v_alloc ty_alloc l_alloc heap' k ty_in ty_out,
    HeapKeysBounded heap ->
    RegularResolvedValShape heap v_alloc ty_alloc ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    RegularResolvedKontShape heap k ty_in ty_out ->
    RegularResolvedKontShape heap' k ty_in ty_out.
Proof.
  intros heap r_alloc v_alloc ty_alloc l_alloc heap' k ty_in ty_out
    HBounded HAllocVal HAlloc HK.
  induction HK; try solve [econstructor; eauto].
  - eapply RRKS_MuAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_MuAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_EffAppFun with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary)
      (eff_arg := eff_arg);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_EffAppArg with
      (gamma := gamma) (omega := omega)
      (ty_arg := ty_arg) (ty_body := ty_body)
      (eff_body := eff_body) (eff_summary := eff_summary);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_PairParEff1 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2)
      (eff_summary2 := eff_summary2);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_PairParEff2 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_PairParFallbackLeft with
      (gamma := gamma) (omega := omega)
      (ty2 := ty2) (eff2 := eff2);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_PairParFallbackRight; eauto.
    eapply RegularResolvedValShape_heap_alloc; eauto.
  - eapply RRKS_Cond with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_t := eff_t) (eff_f := eff_f);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_AssignLoc with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_v := eff_v);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_AssignVal; eauto.
    eapply RegularResolvedValShape_heap_alloc; eauto.
  - eapply RRKS_PlusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_MinusL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_TimesL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_EqL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using RegularResolvedEnvShape_heap_alloc.
  - eapply RRKS_ConcatL with
      (gamma := gamma) (omega := omega) (eff := eff);
      eauto using RegularResolvedEnvShape_heap_alloc.
Qed.

Lemma RegularResolvedStateShape_heap_alloc :
  forall state ty heap r_alloc v_alloc ty_alloc l_alloc heap',
    HeapKeysBounded heap ->
    state_heap state = heap ->
    RegularResolvedValShape heap v_alloc ty_alloc ->
    heap_alloc r_alloc v_alloc heap = (l_alloc, heap') ->
    RegularResolvedStateShape state ty ->
    RegularResolvedStateShape (with_state_heap heap' state) ty.
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
    eapply RRSS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty) (eff := eff);
      eauto using
        RegularResolvedHeapShape_alloc,
        RegularResolvedEnvShape_heap_alloc,
        RegularResolvedKontShape_heap_alloc.
  - subst heap_current.
    simpl.
    eapply RRSS_Return with (ty := ty);
      eauto using
        RegularResolvedHeapShape_alloc,
        RegularResolvedValShape_heap_alloc,
        RegularResolvedKontShape_heap_alloc.
  - subst heap_current.
    simpl.
    eapply RRSS_Done with (ty := ty);
      eauto using
        RegularResolvedHeapShape_alloc,
        RegularResolvedValShape_heap_alloc.
  - subst heap_current.
    simpl.
    eapply RRSS_Error;
      eauto using RegularResolvedHeapShape_alloc.
  - simpl.
    pose proof
      (RegularResolvedStateShape_aligned _ _ HState1)
      as HAlignedLeft.
    pose proof
      (RegularResolvedStateShape_aligned _ _ HState2)
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
    eapply RRSS_PairParRun with
      (heap := heap') (ty1 := ty1) (ty2 := ty2).
    + exact HLeftHeap'.
    + exact HRightHeap'.
    + eapply IHHState1; eauto.
    + eapply IHHState2; eauto.
    + eapply RegularResolvedKontShape_heap_alloc; eauto.
      rewrite <- HShapeHeap. exact H1.
Qed.
