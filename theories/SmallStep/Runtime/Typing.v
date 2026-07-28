From stdpp Require Import gmap.
From Stdlib Require Import List.
From Stdlib Require Import Ascii.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.
Require Import theories.SmallStep.Runtime.Machine.
Require Import theories.SmallStep.Typing.Judgments.
Require Import theories.SmallStep.Typing.Types.

Import ListNotations.

Definition NRhoModels (omega : NRgnCtx) (rho : Rho) : Prop :=
  forall x,
    In x omega ->
    exists r,
      rho_lookup x rho = Some r.

Definition NRegionResolves (rho : Rho) (rgn : RegionExpr)
    (r : RegionId) : Prop :=
  eval_region rho rgn = Some r.

Lemma NRhoModels_eval_region :
  forall omega rho rgn,
    NRhoModels omega rho ->
    region_expr_wf omega rgn ->
    exists r,
      eval_region rho rgn = Some r.
Proof.
  intros omega rho rgn HRho HWF.
  inversion HWF; subst.
  - exists r. reflexivity.
  - apply HRho. assumption.
Qed.

Inductive NValHasType : Rho -> Heap -> NVal -> NTy -> Prop :=
| NVT_Nat :
    forall rho heap n,
      NValHasType rho heap (VNat n) TyNat
| NVT_Bool :
    forall rho heap b,
      NValHasType rho heap (VBool b) TyBool
| NVT_Unit :
    forall rho heap,
      NValHasType rho heap VUnit TyUnit
| NVT_Summary :
    forall rho heap theta,
      NValHasType rho heap (VSummary theta) TyEffect
| NVT_Pair :
    forall rho heap v1 v2 ty1 ty2,
      NValHasType rho heap v1 ty1 ->
      NValHasType rho heap v2 ty2 ->
      NValHasType rho heap (VPair v1 v2) (TyPair ty1 ty2)
| NVT_Loc :
    forall rho heap rgn ty r l cell,
      eval_region_type rho rgn = Some r ->
      heap_lookup r l heap = Some cell ->
      NValHasType rho heap cell ty ->
      NValHasType rho heap (VLoc r l) (TyRef rgn ty)
| NVT_Closure :
    forall rho heap closure_env closure_rho f x ec ee
      gamma omega ty_arg ty_body eff_body eff_summary,
      NEnvHasType closure_rho heap closure_env gamma ->
      NRhoModels omega closure_rho ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      NValHasType rho heap
        (VClosure closure_env closure_rho f x ec ee)
        (TyArrow ty_arg eff_body ty_body eff_summary)
| NVT_RegionClosure :
    forall rho heap closure_env closure_rho x e gamma omega ty eff,
      NEnvHasType closure_rho heap closure_env gamma ->
      NRhoModels omega closure_rho ->
      NTcExp gamma (x :: omega) e ty eff ->
      NValHasType rho heap
        (VRegionClosure closure_env closure_rho x e)
        (TyForallRgn (close_static_effect x eff) (close_ty x ty))
with NEnvHasType : Rho -> Heap -> NEnv -> NCtx -> Prop :=
| NET_EnvNil :
    forall rho heap,
      NEnvHasType rho heap EnvNil []
| NET_EnvCons :
    forall rho heap x v env ty gamma,
      NValHasType rho heap v ty ->
      NEnvHasType rho heap env gamma ->
      NEnvHasType rho heap (EnvCons x v env) ((x, ty) :: gamma).

Scheme NValHasType_ind' := Induction for NValHasType Sort Prop
with NEnvHasType_ind' := Induction for NEnvHasType Sort Prop.

Combined Scheme NValHasType_NEnvHasType_ind
  from NValHasType_ind', NEnvHasType_ind'.

Definition NRuntimeHeapShape (rho : Rho) (heap : Heap) : Prop :=
  forall r l v,
    heap_lookup r l heap = Some v ->
    exists ty,
      NValHasType rho heap v ty.

Definition NRuntimeEnvShape
    (rho : Rho) (heap : Heap) (env : NEnv) (gamma : NCtx) : Prop :=
  NEnvHasType rho heap env gamma.

Lemma NValHasType_ref_region :
  forall rho heap r l rgn ty,
    NValHasType rho heap (VLoc r l) (TyRef rgn ty) ->
    eval_region_type rho rgn = Some r.
Proof.
  intros rho heap r l rgn ty HTy.
  inversion HTy; subst.
  assumption.
Qed.

Lemma NValHasType_ref_lookup :
  forall rho heap r l rgn ty,
    NValHasType rho heap (VLoc r l) (TyRef rgn ty) ->
    exists cell,
      heap_lookup r l heap = Some cell /\
      NValHasType rho heap cell ty.
Proof.
  intros rho heap r l rgn ty HTy.
  inversion HTy; subst.
  exists cell.
  split; assumption.
Qed.

Lemma NEnvHasType_lookup :
  forall rho heap env gamma x ty,
    NEnvHasType rho heap env gamma ->
    ctx_binds x ty gamma ->
    exists v,
      env_lookup x env = Some v /\
      NValHasType rho heap v ty.
Proof.
  intros rho heap env gamma x ty HEnv.
  induction HEnv as
    [rho heap
    | rho heap y v env ty_y gamma HV HEnv IH];
    intros HBind.
  - inversion HBind.
  - unfold ctx_binds in HBind.
    simpl in HBind.
    simpl.
    destruct (ascii_dec x y) as [HEq | HNe].
    + inversion HBind; subst.
      exists v. split; [reflexivity | assumption].
    + apply IH. exact HBind.
Qed.

Lemma NEnvHasType_extend :
  forall rho heap env gamma x v ty,
    NValHasType rho heap v ty ->
    NEnvHasType rho heap env gamma ->
    NEnvHasType rho heap (env_extend x v env) ((x, ty) :: gamma).
Proof.
  intros rho heap env gamma x v ty HV HEnv.
  constructor; assumption.
Qed.

Lemma NRhoModels_extend :
  forall omega rho x r,
    NRhoModels omega rho ->
    NRhoModels (x :: omega) (rho_extend x r rho).
Proof.
  intros omega rho x r HRho y HIn.
  simpl in HIn.
  destruct HIn as [HHead | HTail].
  - subst y.
    unfold rho_extend, rho_lookup, region_var_expr, update_R, find_R.
    simpl.
    exists r.
    apply lookup_insert_Some.
    left. split; reflexivity.
  - unfold rho_extend, rho_lookup, region_var_expr, update_R, find_R.
    simpl.
    destruct (ascii_dec y x) as [HEq | HNe].
    + subst y.
      exists r.
      apply lookup_insert_Some.
      left. split; reflexivity.
    + destruct (HRho y HTail) as (r0 & HRhoLookup).
      exists r0.
      apply lookup_insert_Some.
      right. split.
      * intro H. apply HNe. symmetry. assumption.
      * assumption.
Qed.

Lemma eval_region_rho_extend_head :
  forall rho x r,
    eval_region (rho_extend x r rho) (region_var_expr x) = Some r.
Proof.
  intros rho x r.
  unfold eval_region, rho_extend, region_var_expr, rho_lookup, update_R, find_R.
  simpl.
  apply lookup_insert_Some.
  left. split; reflexivity.
Qed.

Inductive NKontHasType :
    NCtx -> NRgnCtx -> Rho -> Heap -> NKont -> NTy -> Prop :=
| NKT_Done :
    forall gamma omega rho heap ty,
      NKontHasType gamma omega rho heap KDone ty
| NKT_MuAppFun :
    forall gamma omega rho heap ea env k
      ty_arg ty_body eff_body eff_summary eff_arg,
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega ea ty_arg eff_arg ->
      NKontHasType gamma omega rho heap k ty_body ->
      NKontHasType gamma omega rho heap
        (KMuAppFun ea env rho k)
        (TyArrow ty_arg eff_body ty_body eff_summary)
| NKT_MuAppArg :
    forall gamma omega rho heap closure_env closure_rho f x ec ee k
      gamma_closure omega_closure ty_arg ty_body eff_body eff_summary,
      NRuntimeEnvShape closure_rho heap closure_env gamma_closure ->
      NRhoModels omega_closure closure_rho ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure ec ty_body eff_body ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure ee TyEffect eff_summary ->
      NKontHasType gamma omega rho heap k ty_body ->
      NKontHasType gamma omega rho heap
        (KMuAppArg closure_env closure_rho f x ec ee k)
        ty_arg
| NKT_EffAppFun :
    forall gamma omega rho heap ea env k
      ty_arg ty_body eff_body eff_summary eff_arg,
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega ea ty_arg eff_arg ->
      NKontHasType gamma omega rho heap k TyEffect ->
      NKontHasType gamma omega rho heap
        (KEffAppFun ea env rho k)
        (TyArrow ty_arg eff_body ty_body eff_summary)
| NKT_EffAppArg :
    forall gamma omega rho heap closure_env closure_rho f x ec ee k
      gamma_closure omega_closure ty_arg ty_body eff_body eff_summary,
      NRuntimeEnvShape closure_rho heap closure_env gamma_closure ->
      NRhoModels omega_closure closure_rho ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure ec ty_body eff_body ->
      NTcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure ee TyEffect eff_summary ->
      NKontHasType gamma omega rho heap k TyEffect ->
      NKontHasType gamma omega rho heap
        (KEffAppArg closure_env closure_rho f x ec ee k)
        ty_arg
| NKT_PairParEff1 :
    forall gamma omega rho heap ef1 ea1 ef2 ea2 env k
      ty1 ty2 eff1 eff2 eff_summary2,
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      NTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      NTcExp gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      NKontHasType gamma omega rho heap k (TyPair ty1 ty2) ->
      NKontHasType gamma omega rho heap
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
        TyEffect
| NKT_PairParEff2 :
    forall gamma omega rho heap ef1 ea1 ef2 ea2 env theta1 k
      ty1 ty2 eff1 eff2,
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      NTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      NKontHasType gamma omega rho heap k (TyPair ty1 ty2) ->
      NKontHasType gamma omega rho heap
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
        TyEffect
| NKT_RgnApp :
    forall gamma omega rho heap r k eff ty,
      region_expr_wf omega r ->
      NKontHasType gamma omega rho heap k (open_ty r ty) ->
      NKontHasType gamma omega rho heap
        (KRgnApp r rho k)
        (TyForallRgn eff ty)
| NKT_Cond :
    forall gamma omega rho heap et ef env k ty eff_t eff_f,
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega et ty eff_t ->
      NTcExp gamma omega ef ty eff_f ->
      NKontHasType gamma omega rho heap k ty ->
      NKontHasType gamma omega rho heap
        (KCond et ef env rho k)
        TyBool
| NKT_Ref :
    forall gamma omega rho heap rgn r_val k ty,
      eval_region rho rgn = Some r_val ->
      NKontHasType gamma omega rho heap k
        (TyRef (region_expr_to_type rgn) ty) ->
      NKontHasType gamma omega rho heap
        (KRef r_val k)
        ty
| NKT_Deref :
    forall gamma omega rho heap rgn k ty,
      NKontHasType gamma omega rho heap k ty ->
      NKontHasType gamma omega rho heap
        (KDeref rgn k)
        (TyRef (region_expr_to_type rgn) ty)
| NKT_AssignLoc :
    forall gamma omega rho heap rgn ev env k ty eff_v,
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega ev ty eff_v ->
      NKontHasType gamma omega rho heap k TyUnit ->
      NKontHasType gamma omega rho heap
        (KAssignLoc rgn ev env rho k)
        (TyRef (region_expr_to_type rgn) ty)
| NKT_AssignVal :
    forall gamma omega rho heap rgn loc k ty,
      NValHasType rho heap loc (TyRef (region_expr_to_type rgn) ty) ->
      NKontHasType gamma omega rho heap k TyUnit ->
      NKontHasType gamma omega rho heap
        (KAssignVal rgn loc k)
        ty
| NKT_PlusL :
    forall gamma omega rho heap e2 env k eff,
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega e2 TyNat eff ->
      NKontHasType gamma omega rho heap k TyNat ->
      NKontHasType gamma omega rho heap
        (KPlusL e2 env rho k)
        TyNat
| NKT_PlusR :
    forall gamma omega rho heap n k,
      NKontHasType gamma omega rho heap k TyNat ->
      NKontHasType gamma omega rho heap
        (KPlusR n k)
        TyNat
| NKT_MinusL :
    forall gamma omega rho heap e2 env k eff,
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega e2 TyNat eff ->
      NKontHasType gamma omega rho heap k TyNat ->
      NKontHasType gamma omega rho heap
        (KMinusL e2 env rho k)
        TyNat
| NKT_MinusR :
    forall gamma omega rho heap n k,
      NKontHasType gamma omega rho heap k TyNat ->
      NKontHasType gamma omega rho heap
        (KMinusR n k)
        TyNat
| NKT_TimesL :
    forall gamma omega rho heap e2 env k eff,
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega e2 TyNat eff ->
      NKontHasType gamma omega rho heap k TyNat ->
      NKontHasType gamma omega rho heap
        (KTimesL e2 env rho k)
        TyNat
| NKT_TimesR :
    forall gamma omega rho heap n k,
      NKontHasType gamma omega rho heap k TyNat ->
      NKontHasType gamma omega rho heap
        (KTimesR n k)
        TyNat
| NKT_EqL :
    forall gamma omega rho heap e2 env k eff,
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega e2 TyNat eff ->
      NKontHasType gamma omega rho heap k TyBool ->
      NKontHasType gamma omega rho heap
        (KEqL e2 env rho k)
        TyNat
| NKT_EqR :
    forall gamma omega rho heap n k,
      NKontHasType gamma omega rho heap k TyBool ->
      NKontHasType gamma omega rho heap
        (KEqR n k)
        TyNat
| NKT_ReadConc :
    forall gamma omega rho heap k rgn ty,
      NKontHasType gamma omega rho heap k TyEffect ->
      NKontHasType gamma omega rho heap
        (KReadConc k)
        (TyRef rgn ty)
| NKT_WriteConc :
    forall gamma omega rho heap k rgn ty,
      NKontHasType gamma omega rho heap k TyEffect ->
      NKontHasType gamma omega rho heap
        (KWriteConc k)
        (TyRef rgn ty)
| NKT_ConcatL :
    forall gamma omega rho heap e2 env k eff,
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega e2 TyEffect eff ->
      NKontHasType gamma omega rho heap k TyEffect ->
      NKontHasType gamma omega rho heap
        (KConcatL e2 env rho k)
        TyEffect
| NKT_ConcatR :
    forall gamma omega rho heap theta k,
      NKontHasType gamma omega rho heap k TyEffect ->
      NKontHasType gamma omega rho heap
        (KConcatR theta k)
        TyEffect.

Inductive NWTState : NCtx -> NRgnCtx -> NState -> Prop :=
| NWT_Eval :
    forall gamma omega heap env rho e k ty eff,
      NRuntimeHeapShape rho heap ->
      NRuntimeEnvShape rho heap env gamma ->
      NRhoModels omega rho ->
      NTcExp gamma omega e ty eff ->
      NKontHasType gamma omega rho heap k ty ->
      NWTState gamma omega (StEval heap env rho e k)
| NWT_Return :
    forall gamma omega heap rho v k ty,
      NRuntimeHeapShape rho heap ->
      NRhoModels omega rho ->
      NValHasType rho heap v ty ->
      NKontHasType gamma omega rho heap k ty ->
      NWTState gamma omega (StReturn heap v k)
| NWT_Done :
    forall gamma omega heap v rho ty,
      NRuntimeHeapShape rho heap ->
      NRhoModels omega rho ->
      NValHasType rho heap v ty ->
      NWTState gamma omega (StDone heap v)
| NWT_Error :
    forall gamma omega heap rho,
      NRuntimeHeapShape rho heap ->
      NRhoModels omega rho ->
      NWTState gamma omega (StError heap)
| NWT_PairParRun :
    forall gamma omega left_state right_state phi_left phi_right k
      heap rho ty1 ty2,
      state_heap left_state = heap ->
      state_heap right_state = heap ->
      NWTState gamma omega left_state ->
      NWTState gamma omega right_state ->
      NRuntimeHeapShape rho heap ->
      NRhoModels omega rho ->
      NKontHasType gamma omega rho heap k (TyPair ty1 ty2) ->
      NWTState gamma omega
        (StPairParRun left_state right_state phi_left phi_right k).
