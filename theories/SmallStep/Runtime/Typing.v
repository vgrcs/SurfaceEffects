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

Definition RhoModels (omega : RgnCtx) (rho : Rho) : Prop :=
  forall x,
    In x omega ->
    exists r,
      rho_lookup x rho = Some r.

Definition RegionResolves (rho : Rho) (rgn : RegionExpr)
    (r : RegionId) : Prop :=
  eval_region rho rgn = Some r.

Lemma RhoModels_eval_region :
  forall omega rho rgn,
    RhoModels omega rho ->
    region_expr_wf omega rgn ->
    exists r,
      eval_region rho rgn = Some r.
Proof.
  intros omega rho rgn HRho HWF.
  inversion HWF; subst.
  - exists r. reflexivity.
  - apply HRho. assumption.
Qed.

Inductive ValHasType : Rho -> Heap -> Val -> Ty -> Prop :=
| VT_Nat :
    forall rho heap n,
      ValHasType rho heap (VNat n) TyNat
| VT_Bool :
    forall rho heap b,
      ValHasType rho heap (VBool b) TyBool
| VT_Unit :
    forall rho heap,
      ValHasType rho heap VUnit TyUnit
| VT_Summary :
    forall rho heap theta,
      ValHasType rho heap (VSummary theta) TyEffect
| VT_Pair :
    forall rho heap v1 v2 ty1 ty2,
      ValHasType rho heap v1 ty1 ->
      ValHasType rho heap v2 ty2 ->
      ValHasType rho heap (VPair v1 v2) (TyPair ty1 ty2)
| VT_Loc :
    forall rho heap rgn ty r l cell,
      eval_region_type rho rgn = Some r ->
      heap_lookup r l heap = Some cell ->
      ValHasType rho heap cell ty ->
      ValHasType rho heap (VLoc r l) (TyRef rgn ty)
| VT_Closure :
    forall rho heap closure_env closure_rho f x ec ee
      gamma omega ty_arg ty_body eff_body eff_summary,
      EnvHasType closure_rho heap closure_env gamma ->
      RhoModels omega closure_rho ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ec ty_body eff_body ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
        omega ee TyEffect eff_summary ->
      ValHasType rho heap
        (VClosure closure_env closure_rho f x ec ee)
        (TyArrow ty_arg eff_body ty_body eff_summary)
| VT_RegionClosure :
    forall rho heap closure_env closure_rho x e gamma omega ty eff,
      EnvHasType closure_rho heap closure_env gamma ->
      RhoModels omega closure_rho ->
      TcExp gamma (x :: omega) e ty eff ->
      ValHasType rho heap
        (VRegionClosure closure_env closure_rho x e)
        (TyForallRgn (close_static_effect x eff) (close_ty x ty))
with EnvHasType : Rho -> Heap -> Env -> Ctx -> Prop :=
| ET_EnvNil :
    forall rho heap,
      EnvHasType rho heap EnvNil []
| ET_EnvCons :
    forall rho heap x v env ty gamma,
      ValHasType rho heap v ty ->
      EnvHasType rho heap env gamma ->
      EnvHasType rho heap (EnvCons x v env) ((x, ty) :: gamma).

Scheme ValHasType_ind' := Induction for ValHasType Sort Prop
with EnvHasType_ind' := Induction for EnvHasType Sort Prop.

Combined Scheme ValHasType_EnvHasType_ind
  from ValHasType_ind', EnvHasType_ind'.

Definition RuntimeHeapShape (rho : Rho) (heap : Heap) : Prop :=
  forall r l v,
    heap_lookup r l heap = Some v ->
    exists ty,
      ValHasType rho heap v ty.

Definition RuntimeEnvShape
    (rho : Rho) (heap : Heap) (env : Env) (gamma : Ctx) : Prop :=
  EnvHasType rho heap env gamma.

Lemma ValHasType_ref_region :
  forall rho heap r l rgn ty,
    ValHasType rho heap (VLoc r l) (TyRef rgn ty) ->
    eval_region_type rho rgn = Some r.
Proof.
  intros rho heap r l rgn ty HTy.
  inversion HTy; subst.
  assumption.
Qed.

Lemma ValHasType_ref_lookup :
  forall rho heap r l rgn ty,
    ValHasType rho heap (VLoc r l) (TyRef rgn ty) ->
    exists cell,
      heap_lookup r l heap = Some cell /\
      ValHasType rho heap cell ty.
Proof.
  intros rho heap r l rgn ty HTy.
  inversion HTy; subst.
  exists cell.
  split; assumption.
Qed.

Lemma EnvHasType_lookup :
  forall rho heap env gamma x ty,
    EnvHasType rho heap env gamma ->
    ctx_binds x ty gamma ->
    exists v,
      env_lookup x env = Some v /\
      ValHasType rho heap v ty.
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

Lemma EnvHasType_extend :
  forall rho heap env gamma x v ty,
    ValHasType rho heap v ty ->
    EnvHasType rho heap env gamma ->
    EnvHasType rho heap (env_extend x v env) ((x, ty) :: gamma).
Proof.
  intros rho heap env gamma x v ty HV HEnv.
  constructor; assumption.
Qed.

Lemma RhoModels_extend :
  forall omega rho x r,
    RhoModels omega rho ->
    RhoModels (x :: omega) (rho_extend x r rho).
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

Inductive KontHasType :
    Ctx -> RgnCtx -> Rho -> Heap -> Kont -> Ty -> Prop :=
| KT_Done :
    forall gamma omega rho heap ty,
      KontHasType gamma omega rho heap KDone ty
| KT_MuAppFun :
    forall gamma omega rho heap ea env k
      ty_arg ty_body eff_body eff_summary eff_arg,
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega ea ty_arg eff_arg ->
      KontHasType gamma omega rho heap k ty_body ->
      KontHasType gamma omega rho heap
        (KMuAppFun ea env rho k)
        (TyArrow ty_arg eff_body ty_body eff_summary)
| KT_MuAppArg :
    forall gamma omega rho heap closure_env closure_rho f x ec ee k
      gamma_closure omega_closure ty_arg ty_body eff_body eff_summary,
      RuntimeEnvShape closure_rho heap closure_env gamma_closure ->
      RhoModels omega_closure closure_rho ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure ec ty_body eff_body ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure ee TyEffect eff_summary ->
      KontHasType gamma omega rho heap k ty_body ->
      KontHasType gamma omega rho heap
        (KMuAppArg closure_env closure_rho f x ec ee k)
        ty_arg
| KT_EffAppFun :
    forall gamma omega rho heap ea env k
      ty_arg ty_body eff_body eff_summary eff_arg,
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega ea ty_arg eff_arg ->
      KontHasType gamma omega rho heap k TyEffect ->
      KontHasType gamma omega rho heap
        (KEffAppFun ea env rho k)
        (TyArrow ty_arg eff_body ty_body eff_summary)
| KT_EffAppArg :
    forall gamma omega rho heap closure_env closure_rho f x ec ee k
      gamma_closure omega_closure ty_arg ty_body eff_body eff_summary,
      RuntimeEnvShape closure_rho heap closure_env gamma_closure ->
      RhoModels omega_closure closure_rho ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure ec ty_body eff_body ->
      TcExp
        ((x, ty_arg) ::
          (f, TyArrow ty_arg eff_body ty_body eff_summary) ::
          gamma_closure)
        omega_closure ee TyEffect eff_summary ->
      KontHasType gamma omega rho heap k TyEffect ->
      KontHasType gamma omega rho heap
        (KEffAppArg closure_env closure_rho f x ec ee k)
        ty_arg
| KT_PairParEff1 :
    forall gamma omega rho heap ef1 ea1 ef2 ea2 env k
      ty1 ty2 eff1 eff2 eff_summary2,
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      TcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      TcExp gamma omega (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      KontHasType gamma omega rho heap k (TyPair ty1 ty2) ->
      KontHasType gamma omega rho heap
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
        TyEffect
| KT_PairParEff2 :
    forall gamma omega rho heap ef1 ea1 ef2 ea2 env theta1 k
      ty1 ty2 eff1 eff2,
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      TcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      KontHasType gamma omega rho heap k (TyPair ty1 ty2) ->
      KontHasType gamma omega rho heap
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
        TyEffect
| KT_RgnApp :
    forall gamma omega rho heap r k eff ty,
      region_expr_wf omega r ->
      KontHasType gamma omega rho heap k (open_ty r ty) ->
      KontHasType gamma omega rho heap
        (KRgnApp r rho k)
        (TyForallRgn eff ty)
| KT_Cond :
    forall gamma omega rho heap et ef env k ty eff_t eff_f,
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega et ty eff_t ->
      TcExp gamma omega ef ty eff_f ->
      KontHasType gamma omega rho heap k ty ->
      KontHasType gamma omega rho heap
        (KCond et ef env rho k)
        TyBool
| KT_Ref :
    forall gamma omega rho heap rgn r_val k ty,
      eval_region rho rgn = Some r_val ->
      KontHasType gamma omega rho heap k
        (TyRef (region_expr_to_type rgn) ty) ->
      KontHasType gamma omega rho heap
        (KRef r_val k)
        ty
| KT_Deref :
    forall gamma omega rho heap rgn k ty,
      KontHasType gamma omega rho heap k ty ->
      KontHasType gamma omega rho heap
        (KDeref rgn k)
        (TyRef (region_expr_to_type rgn) ty)
| KT_AssignLoc :
    forall gamma omega rho heap rgn ev env k ty eff_v,
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega ev ty eff_v ->
      KontHasType gamma omega rho heap k TyUnit ->
      KontHasType gamma omega rho heap
        (KAssignLoc rgn ev env rho k)
        (TyRef (region_expr_to_type rgn) ty)
| KT_AssignVal :
    forall gamma omega rho heap rgn loc k ty,
      ValHasType rho heap loc (TyRef (region_expr_to_type rgn) ty) ->
      KontHasType gamma omega rho heap k TyUnit ->
      KontHasType gamma omega rho heap
        (KAssignVal rgn loc k)
        ty
| KT_PlusL :
    forall gamma omega rho heap e2 env k eff,
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega e2 TyNat eff ->
      KontHasType gamma omega rho heap k TyNat ->
      KontHasType gamma omega rho heap
        (KPlusL e2 env rho k)
        TyNat
| KT_PlusR :
    forall gamma omega rho heap n k,
      KontHasType gamma omega rho heap k TyNat ->
      KontHasType gamma omega rho heap
        (KPlusR n k)
        TyNat
| KT_MinusL :
    forall gamma omega rho heap e2 env k eff,
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega e2 TyNat eff ->
      KontHasType gamma omega rho heap k TyNat ->
      KontHasType gamma omega rho heap
        (KMinusL e2 env rho k)
        TyNat
| KT_MinusR :
    forall gamma omega rho heap n k,
      KontHasType gamma omega rho heap k TyNat ->
      KontHasType gamma omega rho heap
        (KMinusR n k)
        TyNat
| KT_TimesL :
    forall gamma omega rho heap e2 env k eff,
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega e2 TyNat eff ->
      KontHasType gamma omega rho heap k TyNat ->
      KontHasType gamma omega rho heap
        (KTimesL e2 env rho k)
        TyNat
| KT_TimesR :
    forall gamma omega rho heap n k,
      KontHasType gamma omega rho heap k TyNat ->
      KontHasType gamma omega rho heap
        (KTimesR n k)
        TyNat
| KT_EqL :
    forall gamma omega rho heap e2 env k eff,
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega e2 TyNat eff ->
      KontHasType gamma omega rho heap k TyBool ->
      KontHasType gamma omega rho heap
        (KEqL e2 env rho k)
        TyNat
| KT_EqR :
    forall gamma omega rho heap n k,
      KontHasType gamma omega rho heap k TyBool ->
      KontHasType gamma omega rho heap
        (KEqR n k)
        TyNat
| KT_ReadConc :
    forall gamma omega rho heap k rgn ty,
      KontHasType gamma omega rho heap k TyEffect ->
      KontHasType gamma omega rho heap
        (KReadConc k)
        (TyRef rgn ty)
| KT_WriteConc :
    forall gamma omega rho heap k rgn ty,
      KontHasType gamma omega rho heap k TyEffect ->
      KontHasType gamma omega rho heap
        (KWriteConc k)
        (TyRef rgn ty)
| KT_ConcatL :
    forall gamma omega rho heap e2 env k eff,
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega e2 TyEffect eff ->
      KontHasType gamma omega rho heap k TyEffect ->
      KontHasType gamma omega rho heap
        (KConcatL e2 env rho k)
        TyEffect
| KT_ConcatR :
    forall gamma omega rho heap theta k,
      KontHasType gamma omega rho heap k TyEffect ->
      KontHasType gamma omega rho heap
        (KConcatR theta k)
        TyEffect.

Inductive WTState : Ctx -> RgnCtx -> State -> Prop :=
| WT_Eval :
    forall gamma omega heap env rho e k ty eff,
      RuntimeHeapShape rho heap ->
      RuntimeEnvShape rho heap env gamma ->
      RhoModels omega rho ->
      TcExp gamma omega e ty eff ->
      KontHasType gamma omega rho heap k ty ->
      WTState gamma omega (StEval heap env rho e k)
| WT_Return :
    forall gamma omega heap rho v k ty,
      RuntimeHeapShape rho heap ->
      RhoModels omega rho ->
      ValHasType rho heap v ty ->
      KontHasType gamma omega rho heap k ty ->
      WTState gamma omega (StReturn heap v k)
| WT_Done :
    forall gamma omega heap v rho ty,
      RuntimeHeapShape rho heap ->
      RhoModels omega rho ->
      ValHasType rho heap v ty ->
      WTState gamma omega (StDone heap v)
| WT_Error :
    forall gamma omega heap rho,
      RuntimeHeapShape rho heap ->
      RhoModels omega rho ->
      WTState gamma omega (StError heap)
| WT_PairParRun :
    forall gamma omega left_state right_state phi_left phi_right k
      heap rho ty1 ty2,
      state_heap left_state = heap ->
      state_heap right_state = heap ->
      WTState gamma omega left_state ->
      WTState gamma omega right_state ->
      RuntimeHeapShape rho heap ->
      RhoModels omega rho ->
      KontHasType gamma omega rho heap k (TyPair ty1 ty2) ->
      WTState gamma omega
        (StPairParRun left_state right_state phi_left phi_right k).
