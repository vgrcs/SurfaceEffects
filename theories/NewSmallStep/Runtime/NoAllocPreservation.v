From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.
Require Import theories.NewSmallStep.Runtime.HeapFacts.
Require Import theories.NewSmallStep.Runtime.HeapNeutral.
Require Import theories.NewSmallStep.Runtime.Machine.
Require Import theories.NewSmallStep.Runtime.RegularPreservation.
Require Import theories.NewSmallStep.Runtime.RegularStateShape.
Require Import theories.NewSmallStep.Runtime.Trace.
Require Import theories.NewSmallStep.Runtime.Typing.
Require Import theories.NewSmallStep.Typing.Judgments.
Require Import theories.NewSmallStep.Typing.Regularity.
Require Import theories.NewSmallStep.Typing.Resolve.
Require Import theories.NewSmallStep.Typing.Types.

Import ListNotations.

Inductive NNoAllocKontShape :
    NStoreTyping -> NKont -> NTy -> NTy -> Prop :=
| NNAKS_Done :
    forall store ty,
      NNoAllocKontShape store KDone ty ty
| NNAKS_MuAppFun :
    forall store ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res
      eff_arg eff_arg_res ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty_arg ty_arg_res ->
      NResolveStaticEffect rho eff_body eff_body_res ->
      NResolveTy rho ty_body ty_body_res ->
      NResolveStaticEffect rho eff_summary eff_summary_res ->
      NCheckedTcExp gamma omega ea ty_arg eff_arg ->
      NResolveStaticEffect rho eff_arg eff_arg_res ->
      static_noalloc eff_arg_res ->
      static_noalloc eff_body_res ->
      NNoAllocKontShape store k ty_body_res ty_out ->
      NNoAllocKontShape store
        (KMuAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| NNAKS_MuAppArg :
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
      static_noalloc eff_body_res ->
      NNoAllocKontShape store k ty_body_res ty_out ->
      NNoAllocKontShape store
        (KMuAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| NNAKS_EffAppFun :
    forall store ea env rho k gamma omega
      ty_arg ty_arg_res ty_body ty_body_res
      eff_body eff_body_res eff_summary eff_summary_res
      eff_arg eff_arg_res ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty_arg ty_arg_res ->
      NResolveStaticEffect rho eff_body eff_body_res ->
      NResolveTy rho ty_body ty_body_res ->
      NResolveStaticEffect rho eff_summary eff_summary_res ->
      NCheckedTcExp gamma omega ea ty_arg eff_arg ->
      NResolveStaticEffect rho eff_arg eff_arg_res ->
      static_noalloc eff_arg_res ->
      static_noalloc eff_summary_res ->
      NNoAllocKontShape store k TyEffect ty_out ->
      NNoAllocKontShape store
        (KEffAppFun ea env rho k)
        (TyArrow ty_arg_res eff_body_res ty_body_res eff_summary_res)
        ty_out
| NNAKS_EffAppArg :
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
      static_noalloc eff_summary_res ->
      NNoAllocKontShape store k TyEffect ty_out ->
      NNoAllocKontShape store
        (KEffAppArg closure_env closure_rho f x ec ee k)
        ty_arg_res
        ty_out
| NNAKS_PairParEff1 :
    forall store ef1 ea1 ef2 ea2 env rho k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff1_res eff2 eff2_res
      eff_summary2 eff_summary2_res ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty1 ty1_res ->
      NResolveTy rho ty2 ty2_res ->
      NCheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      NCheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      NCheckedTcExp gamma omega
        (EEffApp ef2 ea2) TyEffect eff_summary2 ->
      NResolveStaticEffect rho eff1 eff1_res ->
      NResolveStaticEffect rho eff2 eff2_res ->
      NResolveStaticEffect rho eff_summary2 eff_summary2_res ->
      static_noalloc eff1_res ->
      static_noalloc eff2_res ->
      static_noalloc eff_summary2_res ->
      NNoAllocKontShape store k (TyPair ty1_res ty2_res) ty_out ->
      NNoAllocKontShape store
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)
        TyEffect
        ty_out
| NNAKS_PairParEff2 :
    forall store ef1 ea1 ef2 ea2 env rho theta1 k gamma omega
      ty1 ty1_res ty2 ty2_res eff1 eff1_res eff2 eff2_res ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty1 ty1_res ->
      NResolveTy rho ty2 ty2_res ->
      NCheckedTcExp gamma omega (EMuApp ef1 ea1) ty1 eff1 ->
      NCheckedTcExp gamma omega (EMuApp ef2 ea2) ty2 eff2 ->
      NResolveStaticEffect rho eff1 eff1_res ->
      NResolveStaticEffect rho eff2 eff2_res ->
      static_noalloc eff1_res ->
      static_noalloc eff2_res ->
      NNoAllocKontShape store k (TyPair ty1_res ty2_res) ty_out ->
      NNoAllocKontShape store
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)
        TyEffect
        ty_out
| NNAKS_RgnApp :
    forall store r arg_rho r_val k eff ty ty_out,
      eval_region arg_rho r = Some r_val ->
      static_noalloc
        (open_static_effect_type (region_const_type r_val) eff) ->
      NNoAllocKontShape store k
        (open_ty_type (region_const_type r_val) ty)
        ty_out ->
      NNoAllocKontShape store
        (KRgnApp r arg_rho k)
        (TyForallRgn eff ty)
        ty_out
| NNAKS_Cond :
    forall store et ef env rho k gamma omega ty ty_res
      eff_t eff_t_res eff_f eff_f_res ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty ty_res ->
      NCheckedTcExp gamma omega et ty eff_t ->
      NCheckedTcExp gamma omega ef ty eff_f ->
      NResolveStaticEffect rho eff_t eff_t_res ->
      NResolveStaticEffect rho eff_f eff_f_res ->
      static_noalloc eff_t_res ->
      static_noalloc eff_f_res ->
      NNoAllocKontShape store k ty_res ty_out ->
      NNoAllocKontShape store
        (KCond et ef env rho k)
        TyBool
        ty_out
| NNAKS_Deref :
    forall store rgn r ty k ty_out,
      NNoAllocKontShape store k ty ty_out ->
      NNoAllocKontShape store (KDeref rgn k)
        (TyRef (region_const_type r) ty) ty_out
| NNAKS_AssignLoc :
    forall store rgn ev env rho k gamma omega r ty ty_res
      eff_v eff_v_res ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      eval_region rho rgn = Some r ->
      NResolveTy rho ty ty_res ->
      NCheckedTcExp gamma omega ev ty eff_v ->
      NResolveStaticEffect rho eff_v eff_v_res ->
      static_noalloc eff_v_res ->
      NNoAllocKontShape store k TyUnit ty_out ->
      NNoAllocKontShape store
        (KAssignLoc rgn ev env rho k)
        (TyRef (region_const_type r) ty_res)
        ty_out
| NNAKS_AssignVal :
    forall store rgn r ty loc k ty_out,
      NStoreResolvedValShape store loc
        (TyRef (region_const_type r) ty) ->
      NNoAllocKontShape store k TyUnit ty_out ->
      NNoAllocKontShape store
        (KAssignVal rgn loc k)
        ty
        ty_out
| NNAKS_PlusL :
    forall store e2 env rho k gamma omega eff eff_res ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NResolveStaticEffect rho eff eff_res ->
      static_noalloc eff_res ->
      NNoAllocKontShape store k TyNat ty_out ->
      NNoAllocKontShape store
        (KPlusL e2 env rho k)
        TyNat
        ty_out
| NNAKS_PlusR :
    forall store n k ty_out,
      NNoAllocKontShape store k TyNat ty_out ->
      NNoAllocKontShape store (KPlusR n k) TyNat ty_out
| NNAKS_MinusL :
    forall store e2 env rho k gamma omega eff eff_res ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NResolveStaticEffect rho eff eff_res ->
      static_noalloc eff_res ->
      NNoAllocKontShape store k TyNat ty_out ->
      NNoAllocKontShape store
        (KMinusL e2 env rho k)
        TyNat
        ty_out
| NNAKS_MinusR :
    forall store n k ty_out,
      NNoAllocKontShape store k TyNat ty_out ->
      NNoAllocKontShape store (KMinusR n k) TyNat ty_out
| NNAKS_TimesL :
    forall store e2 env rho k gamma omega eff eff_res ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NResolveStaticEffect rho eff eff_res ->
      static_noalloc eff_res ->
      NNoAllocKontShape store k TyNat ty_out ->
      NNoAllocKontShape store
        (KTimesL e2 env rho k)
        TyNat
        ty_out
| NNAKS_TimesR :
    forall store n k ty_out,
      NNoAllocKontShape store k TyNat ty_out ->
      NNoAllocKontShape store (KTimesR n k) TyNat ty_out
| NNAKS_EqL :
    forall store e2 env rho k gamma omega eff eff_res ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyNat eff ->
      NResolveStaticEffect rho eff eff_res ->
      static_noalloc eff_res ->
      NNoAllocKontShape store k TyBool ty_out ->
      NNoAllocKontShape store
        (KEqL e2 env rho k)
        TyNat
        ty_out
| NNAKS_EqR :
    forall store n k ty_out,
      NNoAllocKontShape store k TyBool ty_out ->
      NNoAllocKontShape store (KEqR n k) TyNat ty_out
| NNAKS_ReadConc :
    forall store k r ty ty_out,
      NNoAllocKontShape store k TyEffect ty_out ->
      NNoAllocKontShape store
        (KReadConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| NNAKS_WriteConc :
    forall store k r ty ty_out,
      NNoAllocKontShape store k TyEffect ty_out ->
      NNoAllocKontShape store
        (KWriteConc k)
        (TyRef (region_const_type r) ty)
        ty_out
| NNAKS_ConcatL :
    forall store e2 env rho k gamma omega eff eff_res ty_out,
      NStoreResolvedEnvShape store rho env gamma ->
      NRhoModels omega rho ->
      NCheckedTcExp gamma omega e2 TyEffect eff ->
      NResolveStaticEffect rho eff eff_res ->
      static_noalloc eff_res ->
      NNoAllocKontShape store k TyEffect ty_out ->
      NNoAllocKontShape store
        (KConcatL e2 env rho k)
        TyEffect
        ty_out
| NNAKS_ConcatR :
    forall store theta k ty_out,
      NNoAllocKontShape store k TyEffect ty_out ->
      NNoAllocKontShape store
        (KConcatR theta k)
        TyEffect
        ty_out.

Inductive NNoAllocStateShape :
    NStoreTyping -> NState -> NTy -> Prop :=
| NNAS_Eval :
    forall store heap env rho e k gamma omega ty ty_res
      eff eff_res ty_out,
      NStoreResolvedRuntimeShape heap store env rho gamma ->
      NRhoModels omega rho ->
      NResolveTy rho ty ty_res ->
      NCheckedTcExp gamma omega e ty eff ->
      NResolveStaticEffect rho eff eff_res ->
      static_noalloc eff_res ->
      NNoAllocKontShape store k ty_res ty_out ->
      NNoAllocStateShape store (StEval heap env rho e k) ty_out
| NNAS_Return :
    forall store heap v k ty ty_out,
      NStoreKeysBoundedByHeap heap store ->
      NStoreResolvedHeapShape heap store ->
      NStoreResolvedValShape store v ty ->
      NNoAllocKontShape store k ty ty_out ->
      NNoAllocStateShape store (StReturn heap v k) ty_out
| NNAS_Done :
    forall store heap v ty,
      NStoreKeysBoundedByHeap heap store ->
      NStoreResolvedHeapShape heap store ->
      NStoreResolvedValShape store v ty ->
      NNoAllocStateShape store (StDone heap v) ty
| NNAS_Error :
    forall store heap ty,
      NStoreKeysBoundedByHeap heap store ->
      NStoreResolvedHeapShape heap store ->
      NNoAllocStateShape store (StError heap) ty
| NNAS_PairParRun :
    forall store left_state right_state phi_left phi_right k
      heap ty1 ty2 ty_out,
      state_heap left_state = heap ->
      state_heap right_state = heap ->
      NNoAllocStateShape store left_state ty1 ->
      NNoAllocStateShape store right_state ty2 ->
      NNoAllocKontShape store k (TyPair ty1 ty2) ty_out ->
      NNoAllocStateShape store
        (StPairParRun left_state right_state phi_left phi_right k)
        ty_out.

Lemma NNoAllocKontShape_to_store :
  forall store k ty_in ty_out,
    NNoAllocKontShape store k ty_in ty_out ->
    NStoreResolvedKontShape store k ty_in ty_out.
Proof.
  intros store k ty_in ty_out HKont.
  induction HKont; eauto using NStoreResolvedKontShape.
Qed.

Lemma NNoAllocStateShape_to_store :
  forall store state ty,
    NNoAllocStateShape store state ty ->
    NStoreResolvedStateShape store state ty.
Proof.
  intros store state ty HState.
  induction HState.
  - eapply NSRSS_Eval; eauto using NNoAllocKontShape_to_store.
  - eapply NSRSS_Return; eauto using NNoAllocKontShape_to_store.
  - eapply NSRSS_Done; eauto.
  - eapply NSRSS_Error; eauto.
  - eapply NSRSS_PairParRun; eauto using NNoAllocKontShape_to_store.
Qed.

Lemma NNoAllocStateShape_aligned :
  forall store state ty,
    NNoAllocStateShape store state ty ->
    NStateHeapsAligned state.
Proof.
  intros store state ty HState.
  eapply NStoreResolvedStateShape_aligned.
  eapply NNoAllocStateShape_to_store; eauto.
Qed.

Lemma NNoAllocStateShape_with_state_heap_same :
  forall store state ty heap,
    NNoAllocStateShape store state ty ->
    state_heap state = heap ->
    NNoAllocStateShape store (with_state_heap heap state) ty.
Proof.
  intros store state ty heap HState HHeap.
  rewrite (with_state_heap_aligned_same heap state).
  - exact HState.
  - eapply NNoAllocStateShape_aligned; eauto.
  - exact HHeap.
Qed.

Lemma NNoAllocStateShape_heap_update :
  forall store state ty heap r l old v ty_cell,
    state_heap state = heap ->
    heap_lookup r l heap = Some old ->
    store_ty_lookup r l store = Some ty_cell ->
    NStoreResolvedValShape store v ty_cell ->
    NNoAllocStateShape store state ty ->
    NNoAllocStateShape store
      (with_state_heap (heap_update r l v heap) state)
      ty.
Proof.
  intros store state ty heap r l old v ty_cell
    HStateHeap HOldLookup HStoreLookup HVal HState.
  revert heap r l old v ty_cell
    HStateHeap HOldLookup HStoreLookup HVal.
  induction HState;
    intros heap_current r_update l_update old v_update ty_cell
      HStateHeap HOldLookup HStoreLookup HVal;
    simpl in HStateHeap.
  - subst heap_current.
    simpl.
    eapply NNAS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty) (eff := eff);
      eauto.
    eapply NStoreResolvedRuntimeShape_update; eauto.
  - subst heap_current.
    simpl.
    eapply NNAS_Return with (ty := ty);
      eauto using
        NStoreKeysBoundedByHeap_update,
        NStoreResolvedHeapShape_update.
  - subst heap_current.
    simpl.
    eapply NNAS_Done with (ty := ty);
      eauto using
        NStoreKeysBoundedByHeap_update,
        NStoreResolvedHeapShape_update.
  - subst heap_current.
    simpl.
    eapply NNAS_Error;
      eauto using
        NStoreKeysBoundedByHeap_update,
        NStoreResolvedHeapShape_update.
  - simpl.
    assert (HLeftHeap : state_heap left_state = heap_current)
      by exact HStateHeap.
    assert (HRightHeap : state_heap right_state = heap_current).
    {
      rewrite H0.
      rewrite <- H.
      exact HLeftHeap.
    }
    eapply NNAS_PairParRun with
      (heap := heap_update r_update l_update v_update heap_current)
      (ty1 := ty1) (ty2 := ty2).
    + rewrite state_heap_with_state_heap. reflexivity.
    + rewrite state_heap_with_state_heap. reflexivity.
    + eapply IHHState1; eauto.
    + eapply IHHState2; eauto.
    + exact H1.
Qed.

Definition NNoAllocStepTransport
    (store : NStoreTyping) (state state' : NState) : Prop :=
  forall sibling ty,
    state_heap sibling = state_heap state ->
    NNoAllocStateShape store sibling ty ->
    NNoAllocStateShape store
      (with_state_heap (state_heap state') sibling) ty.

Lemma NNoAllocStepTransport_same :
  forall store state state',
    state_heap state' = state_heap state ->
    NNoAllocStepTransport store state state'.
Proof.
  intros store state state' HHeap sibling ty HSiblingHeap HSibling.
  eapply NNoAllocStateShape_with_state_heap_same; eauto.
  rewrite HHeap.
  exact HSiblingHeap.
Qed.

Lemma NoAllocTrace_label_silent :
  NoAllocTrace (label_trace LSilent).
Proof.
  simpl.
  intros r l HIn.
  contradiction.
Qed.

Lemma NoAllocTrace_label_read :
  forall r l,
    NoAllocTrace (label_trace (LAction (DRead r l))).
Proof.
  simpl.
  intros r l r0 l0 HIn.
  destruct HIn as [HIn | HIn]; [inversion HIn | contradiction].
Qed.

Lemma NoAllocTrace_label_write :
  forall r l,
    NoAllocTrace (label_trace (LAction (DWrite r l))).
Proof.
  simpl.
  intros r l r0 l0 HIn.
  destruct HIn as [HIn | HIn]; [inversion HIn | contradiction].
Qed.

Lemma NResolveStaticEffect_static_noalloc_union_inv :
  forall rho eff1 eff2 eff',
    NResolveStaticEffect rho (static_union eff1 eff2) eff' ->
    static_noalloc eff' ->
    exists eff1' eff2',
      eff' = static_union eff1' eff2' /\
      NResolveStaticEffect rho eff1 eff1' /\
      static_noalloc eff1' /\
      NResolveStaticEffect rho eff2 eff2' /\
      static_noalloc eff2'.
Proof.
  intros rho eff1 eff2 eff' HResolve HNoAlloc.
  destruct
    (NResolveStaticEffect_static_union_inv
      rho eff1 eff2 eff' HResolve)
    as (eff1' & eff2' & HEq & HResolve1 & HResolve2).
  subst eff'.
  exists eff1', eff2'.
  repeat split; eauto.
  - eapply static_noalloc_app_l; eauto.
  - eapply static_noalloc_app_r; eauto.
Qed.

Lemma static_noalloc_cons_tail :
  forall action eff,
    static_noalloc (action :: eff) ->
    static_noalloc eff.
Proof.
  unfold static_noalloc.
  intros action eff HNoAlloc r HIn.
  eapply HNoAlloc.
  simpl. right. exact HIn.
Qed.

Lemma static_noalloc_alloc_cons_false :
  forall r eff,
    static_noalloc (SAlloc r :: eff) ->
    False.
Proof.
  unfold static_noalloc.
  intros r eff HNoAlloc.
  eapply HNoAlloc.
  simpl. left. reflexivity.
Qed.

Ltac normalize_resolved_effect HResolve :=
  match type of HResolve with
  | NResolveStaticEffect _ ?eff_current _ =>
      match goal with
      | HEq : ?eff_shape = eff_current |- _ =>
          rewrite <- HEq in HResolve
      | HEq : eff_current = ?eff_shape |- _ =>
          rewrite HEq in HResolve
      end
  end.

Lemma NNoAllocStateShape_const_preservation :
  forall store heap env rho n k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EConst n) k)
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VNat n) k)
      ty_out.
Proof.
  intros store heap env rho n k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NNAS_Return; eauto using NSRVS_Nat.
Qed.

Lemma NNoAllocStateShape_bool_preservation :
  forall store heap env rho b k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EBool b) k)
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VBool b) k)
      ty_out.
Proof.
  intros store heap env rho b k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NNAS_Return; eauto using NSRVS_Bool.
Qed.

Lemma NNoAllocStateShape_var_preservation :
  forall store heap env rho x v k ty_out,
    env_lookup x env = Some v ->
    NNoAllocStateShape store
      (StEval heap env rho (EVar x) k)
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap v k)
      ty_out.
Proof.
  intros store heap env rho x v k ty_out HLookup HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  inversion HTyped; subst.
  match goal with
  | HBind : ctx_binds x ty gamma |- _ =>
      destruct
        (NStoreResolvedEnvShape_lookup
          store rho env gamma x ty ty_res HEnv HBind HResolve)
        as (v_typed & HLookupTyped & HV)
  end.
  rewrite HLookup in HLookupTyped.
  inversion HLookupTyped; subst.
  eapply NNAS_Return; eauto.
Qed.

Lemma NNoAllocStateShape_mu_preservation :
  forall store heap env rho f x ec ee k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EMu f x ec ee) k)
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VClosure env rho f x ec ee) k)
      ty_out.
Proof.
  intros store heap env rho f x ec ee k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HChecked) as HTyWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  inversion HTyWF; subst.
  eapply NNAS_Return; eauto.
  eapply NSRVS_Closure with
    (gamma := gamma) (omega := omega)
    (ty_arg := ty_arg) (ty_body := ty_body); eauto.
Qed.

Lemma NNoAllocStateShape_lambda_rgn_preservation :
  forall store heap env rho x e k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (ELambdaRgn x e) k)
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VRegionClosure env rho x e) k)
      ty_out.
Proof.
  intros store heap env rho x e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_ctx_wf _ _ _ _ _ HChecked) as HCtxWF.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HChecked) as HTyWF.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  inversion HTyWF; subst.
  eapply NNAS_Return; eauto.
  eapply NSRVS_RegionClosure with
    (gamma := gamma) (omega := omega)
    (ty := ty) (eff := eff); eauto.
  - rewrite H1. exact H4.
  - rewrite H2. exact H11.
  - constructor; eauto.
Qed.

Lemma NNoAllocStateShape_empty_preservation :
  forall store heap env rho k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho EEmpty k)
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VSummary (SummarySet [])) k)
      ty_out.
Proof.
  intros store heap env rho k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NNAS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NNoAllocStateShape_top_preservation :
  forall store heap env rho k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho ETop k)
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VSummary SummaryTop) k)
      ty_out.
Proof.
  intros store heap env rho k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NNAS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NNoAllocStateShape_alloc_abs_preservation :
  forall store heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NNoAllocStateShape store
      (StEval heap env rho (EAllocAbs r) k)
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VSummary (SummarySet [CAllocAbs r_val])) k)
      ty_out.
Proof.
  intros store heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NNAS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NNoAllocStateShape_read_abs_preservation :
  forall store heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NNoAllocStateShape store
      (StEval heap env rho (EReadAbs r) k)
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VSummary (SummarySet [CReadAbs r_val])) k)
      ty_out.
Proof.
  intros store heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NNAS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NNoAllocStateShape_write_abs_preservation :
  forall store heap env rho r r_val k ty_out,
    eval_region rho r = Some r_val ->
    NNoAllocStateShape store
      (StEval heap env rho (EWriteAbs r) k)
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VSummary (SummarySet [CWriteAbs r_val])) k)
      ty_out.
Proof.
  intros store heap env rho r r_val k ty_out HRgn HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  inversion HTyped; subst.
  inversion HResolve; subst.
  eapply NNAS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NNoAllocStateShape_read_conc_preservation :
  forall store heap r l k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VLoc r l) (KReadConc k))
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VSummary (SummarySet [CReadConc r l])) k)
      ty_out.
Proof.
  intros store heap r l k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NNAS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NNoAllocStateShape_write_conc_preservation :
  forall store heap r l k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VLoc r l) (KWriteConc k))
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VSummary (SummarySet [CWriteConc r l])) k)
      ty_out.
Proof.
  intros store heap r l k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NNAS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NNoAllocStateShape_done_preservation :
  forall store heap v ty_out,
    NNoAllocStateShape store
      (StReturn heap v KDone)
      ty_out ->
    NNoAllocStateShape store (StDone heap v) ty_out.
Proof.
  intros store heap v ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NNAS_Done; eauto.
Qed.

Lemma NNoAllocStateShape_cond_true_preservation :
  forall store heap et ef env rho k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VBool true) (KCond et ef env rho k))
      ty_out ->
    NNoAllocStateShape store (StEval heap env rho et k) ty_out.
Proof.
  intros store heap et ef env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Eval; eauto.
  unfold NStoreResolvedRuntimeShape.
  match goal with
  | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
      split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
  end.
Qed.

Lemma NNoAllocStateShape_cond_false_preservation :
  forall store heap et ef env rho k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VBool false) (KCond et ef env rho k))
      ty_out ->
    NNoAllocStateShape store (StEval heap env rho ef k) ty_out.
Proof.
  intros store heap et ef env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Eval; eauto.
  unfold NStoreResolvedRuntimeShape.
  match goal with
  | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
      split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
  end.
Qed.

Lemma NNoAllocStateShape_deref_preservation :
  forall store heap r_static r l v k ty_out,
    heap_lookup r l heap = Some v ->
    NNoAllocStateShape store
      (StReturn heap (VLoc r l) (KDeref r_static k))
      ty_out ->
    NNoAllocStateShape store (StReturn heap v k) ty_out.
Proof.
  intros store heap r_static r l v k ty_out HLookup HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  destruct HHeap as (HHeapToStore & HStoreToHeap).
  match goal with
  | HLookupCell : heap_lookup ?rr ?ll heap = Some v,
    HStoreLookup : store_ty_lookup ?rr ?ll store = Some ?ty_cell |- _ =>
      destruct (HHeapToStore rr ll v HLookupCell) as
        (ty_found & HStoreFound & HShapeFound);
      pose proof
        (store_ty_lookup_deterministic
          store rr ll ty_found ty_cell HStoreFound HStoreLookup)
        as HTyEq;
      subst ty_found;
      eapply NNAS_Return with (ty := ty_cell);
      [ exact HBounded
      | split; [exact HHeapToStore | exact HStoreToHeap]
      | exact HShapeFound
      | eauto ]
  end.
Qed.

Lemma NNoAllocStateShape_assign_loc_preservation :
  forall store heap r_static ev env rho r l k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VLoc r l) (KAssignLoc r_static ev env rho k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho ev (KAssignVal r_static (VLoc r l) k))
      ty_out.
Proof.
  intros store heap r_static ev env rho r l k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Eval; eauto.
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - eapply NNAKS_AssignVal; eauto.
Qed.

Lemma NNoAllocStateShape_assign_val_preservation :
  forall store heap r_static r l v k ty_out,
    NNoAllocStateShape store
      (StReturn heap v (KAssignVal r_static (VLoc r l) k))
      ty_out ->
    NNoAllocStateShape store
      (StReturn (heap_update r l v heap) VUnit k)
      ty_out /\
    NNoAllocStepTransport store
      (StReturn heap v (KAssignVal r_static (VLoc r l) k))
      (StReturn (heap_update r l v heap) VUnit k).
Proof.
  intros store heap r_static r l v k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty_cell ty_out0
      HBounded HHeap HVal HK | | |];
    subst; clear HState.
  inversion HK; subst.
  match goal with
  | HLoc : NStoreResolvedValShape store (VLoc r l)
      (TyRef (region_const_type ?r0) ?ty_loc) |- _ =>
      inversion HLoc; subst
  end.
  destruct HHeap as (HHeapToStore & HStoreToHeap).
  match goal with
  | HStoreLookup : store_ty_lookup ?rr ?ll store = Some ?ty_loc |- _ =>
      destruct (HStoreToHeap rr ll ty_loc HStoreLookup)
        as (old & HOldLookup & _);
      split;
      [ eapply NNAS_Return with (ty := TyUnit);
        [ eapply NStoreKeysBoundedByHeap_update; eauto
        | eapply NStoreResolvedHeapShape_update; eauto;
          split; [exact HHeapToStore | exact HStoreToHeap]
        | constructor
        | assumption ]
      | intros sibling ty_s HSiblingHeap HSibling;
        eapply NNoAllocStateShape_heap_update; eauto;
        simpl in HSiblingHeap; exact HSiblingHeap ]
  end.
Qed.

Lemma NNoAllocStateShape_plus_l_preservation :
  forall store heap n e2 env rho k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VNat n) (KPlusL e2 env rho k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e2 (KPlusR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - eapply NNAKS_PlusR; eauto.
Qed.

Lemma NNoAllocStateShape_plus_r_preservation :
  forall store heap n1 n2 k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VNat n2) (KPlusR n1 k))
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VNat (n1 + n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Return; eauto using NSRVS_Nat.
Qed.

Lemma NNoAllocStateShape_minus_l_preservation :
  forall store heap n e2 env rho k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VNat n) (KMinusL e2 env rho k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e2 (KMinusR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - eapply NNAKS_MinusR; eauto.
Qed.

Lemma NNoAllocStateShape_minus_r_preservation :
  forall store heap n1 n2 k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VNat n2) (KMinusR n1 k))
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VNat (n1 - n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Return; eauto using NSRVS_Nat.
Qed.

Lemma NNoAllocStateShape_times_l_preservation :
  forall store heap n e2 env rho k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VNat n) (KTimesL e2 env rho k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e2 (KTimesR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - eapply NNAKS_TimesR; eauto.
Qed.

Lemma NNoAllocStateShape_times_r_preservation :
  forall store heap n1 n2 k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VNat n2) (KTimesR n1 k))
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VNat (n1 * n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Return; eauto using NSRVS_Nat.
Qed.

Lemma NNoAllocStateShape_eq_l_preservation :
  forall store heap n e2 env rho k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VNat n) (KEqL e2 env rho k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e2 (KEqR n k))
      ty_out.
Proof.
  intros store heap n e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat) (eff := eff);
    eauto using NResolve_Nat.
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - eapply NNAKS_EqR; eauto.
Qed.

Lemma NNoAllocStateShape_eq_r_preservation :
  forall store heap n1 n2 k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VNat n2) (KEqR n1 k))
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VBool (Nat.eqb n1 n2)) k)
      ty_out.
Proof.
  intros store heap n1 n2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Return; eauto using NSRVS_Bool.
Qed.

Lemma NNoAllocStateShape_concat_l_preservation :
  forall store heap theta1 e2 env rho k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e2 (KConcatR theta1 k))
      ty_out.
Proof.
  intros store heap theta1 e2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect) (eff := eff);
    eauto using NResolve_Effect.
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - eapply NNAKS_ConcatR; eauto.
Qed.

Lemma NNoAllocStateShape_concat_r_preservation :
  forall store heap theta1 theta2 k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VSummary theta2) (KConcatR theta1 k))
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VSummary (summary_union theta1 theta2)) k)
      ty_out.
Proof.
  intros store heap theta1 theta2 k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Return; eauto using NSRVS_Summary.
Qed.

Lemma NNoAllocStateShape_mu_app_eval_arg_preservation :
  forall store heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    NNoAllocStateShape store
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KMuAppFun ea env rho k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho ea
        (KMuAppArg closure_env closure_rho f x ec ee k))
      ty_out.
Proof.
  intros store heap env rho ea k closure_env closure_rho f x ec ee
    ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res)
    (eff := eff_arg) (eff_res := eff_arg_res).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - eapply NNAKS_MuAppArg with
      (gamma := gamma0) (omega := omega0)
      (ty_arg := ty_arg0) (ty_body := ty_body0)
      (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma NNoAllocStateShape_eff_app_eval_arg_preservation :
  forall store heap env rho ea k closure_env closure_rho f x ec ee ty_out,
    NNoAllocStateShape store
      (StReturn heap
        (VClosure closure_env closure_rho f x ec ee)
        (KEffAppFun ea env rho k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho ea
        (KEffAppArg closure_env closure_rho f x ec ee k))
      ty_out.
Proof.
  intros store heap env rho ea k closure_env closure_rho f x ec ee
    ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := ty_arg) (ty_res := ty_arg_res)
    (eff := eff_arg) (eff_res := eff_arg_res).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - eapply NNAKS_EffAppArg with
      (gamma := gamma0) (omega := omega0)
      (ty_arg := ty_arg0) (ty_body := ty_body0)
      (eff_body := eff_body0) (eff_summary := eff_summary0);
    eauto.
Qed.

Lemma NNoAllocStateShape_mu_app_body_preservation :
  forall store heap v_arg closure_env closure_rho f x ec ee k ty_out,
    NNoAllocStateShape store
      (StReturn heap v_arg
        (KMuAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap
        (env_extend x v_arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho
        ec
        k)
      ty_out.
Proof.
  intros store heap v_arg closure_env closure_rho f x ec ee k
    ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NNAS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := ty_body) (ty_res := ty_body_res)
    (eff := eff_body) (eff_res := eff_body_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | ]].
    eapply NStoreResolvedEnvShape_extend with
      (ty_res := ty); eauto.
    eapply NStoreResolvedEnvShape_extend with
      (ty_res := TyArrow
        ty eff_body_res ty_body_res eff_summary_res);
      eauto.
    + eapply NResolve_Arrow; eauto.
    + eapply NSRVS_Closure with
        (gamma := gamma) (omega := omega)
        (ty_arg := ty_arg) (ty_body := ty_body); eauto.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma NNoAllocStateShape_eff_app_body_preservation :
  forall store heap v_arg closure_env closure_rho f x ec ee k ty_out,
    NNoAllocStateShape store
      (StReturn heap v_arg
        (KEffAppArg closure_env closure_rho f x ec ee k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap
        (env_extend x v_arg
          (env_extend f
            (VClosure closure_env closure_rho f x ec ee)
            closure_env))
        closure_rho
        ee
        k)
      ty_out.
Proof.
  intros store heap v_arg closure_env closure_rho f x ec ee k
    ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  eapply NNAS_Eval with
    (gamma :=
      (x, ty_arg) ::
      (f, TyArrow ty_arg eff_body ty_body eff_summary) :: gamma)
    (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect)
    (eff := eff_summary) (eff_res := eff_summary_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | ]].
    eapply NStoreResolvedEnvShape_extend with
      (ty_res := ty); eauto.
    eapply NStoreResolvedEnvShape_extend with
      (ty_res := TyArrow
        ty eff_body_res ty_body_res eff_summary_res);
      eauto.
    + eapply NResolve_Arrow; eauto.
    + eapply NSRVS_Closure with
        (gamma := gamma) (omega := omega)
        (ty_arg := ty_arg) (ty_body := ty_body); eauto.
  - assumption.
  - constructor.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma NNoAllocStateShape_pair_par_eff1_preservation :
  forall store heap theta1 ef1 ea1 ef2 ea2 env rho k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VSummary theta1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho (EEffApp ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out.
Proof.
  intros store heap theta1 ef1 ea1 ef2 ea2 env rho k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect)
    (eff := eff_summary2) (eff_res := eff_summary2_res).
  - unfold NStoreResolvedRuntimeShape.
    match goal with
    | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
        split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
    end.
  - assumption.
  - constructor.
  - assumption.
  - assumption.
  - assumption.
  - eapply NNAKS_PairParEff2 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff1) (eff2 := eff2);
    eauto.
Qed.

Lemma NNoAllocStateShape_pair_par_check_pass_preservation :
  forall store heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    NNoAllocStateShape store
      (StPairParRun
        (StEval heap env rho (EMuApp ef1 ea1) KDone)
        (StEval heap env rho (EMuApp ef2 ea2) KDone)
        [] [] k)
      ty_out.
Proof.
  intros store heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out
    HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK; subst.
  inversion HV; subst.
  eapply NNAS_PairParRun with
    (heap := heap) (ty1 := ty1_res) (ty2 := ty2_res);
    simpl; eauto.
  - eapply NNAS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty1) (ty_res := ty1_res)
      (eff := eff1) (eff_res := eff1_res).
    + unfold NStoreResolvedRuntimeShape.
      match goal with
      | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
          split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
      end.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + constructor.
  - eapply NNAS_Eval with
      (gamma := gamma) (omega := omega)
      (ty := ty2) (ty_res := ty2_res)
      (eff := eff2) (eff_res := eff2_res).
    + unfold NStoreResolvedRuntimeShape.
      match goal with
      | HEnvShape : NStoreResolvedEnvShape store rho env gamma |- _ =>
          split; [exact HBounded | split; [exact HHeap | exact HEnvShape]]
      end.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + constructor.
Qed.

Lemma NNoAllocStateShape_pair_par_check_fail_preservation :
  forall store heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out,
    NNoAllocStateShape store
      (StReturn heap (VSummary theta2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
      ty_out ->
    NNoAllocStateShape store (StError heap) ty_out.
Proof.
  intros store heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k ty_out
    HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  eapply NNAS_Error; eauto.
Qed.

Lemma NNoAllocStateShape_pair_par_left_error_preservation :
  forall store heap right_state phi_left phi_right k ty_out,
    NNoAllocStateShape store
      (StPairParRun (StError heap) right_state phi_left phi_right k)
      ty_out ->
    NNoAllocStateShape store (StError heap) ty_out.
Proof.
  intros store heap right_state phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      store0 left_state0 right_state0 phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    clear HState.
  subst left_state0 right_state0 phi_left0 phi_right0 k0 ty_out0.
  simpl in HHeapLeft.
  subst heap0.
  inversion HLeft; subst.
  eapply NNAS_Error; eauto.
Qed.

Lemma NNoAllocStateShape_pair_par_right_error_preservation :
  forall store heap_left v1 heap_right phi_left phi_right k ty_out,
    NNoAllocStateShape store
      (StPairParRun
        (StDone heap_left v1)
        (StError heap_right)
        phi_left phi_right k)
      ty_out ->
    NNoAllocStateShape store (StError heap_right) ty_out.
Proof.
  intros store heap_left v1 heap_right phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      store0 left_state right_state phi_left0 phi_right0 k0 heap
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    clear HState.
  subst left_state right_state phi_left0 phi_right0 k0 ty_out0.
  simpl in HHeapRight.
  subst heap.
  inversion HRight; subst.
  eapply NNAS_Error; eauto.
Qed.

Lemma NNoAllocStateShape_pair_par_done_pass_preservation :
  forall store heap v1 v2 phi_left phi_right k ty_out,
    NNoAllocStateShape store
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    NNoAllocStateShape store
      (StReturn heap (VPair v1 v2) k)
      ty_out.
Proof.
  intros store heap v1 v2 phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      store0 left_state right_state phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    subst; clear HState; simpl in *; subst.
  inversion HLeft as
    [| | store1 heap1 v_left ty_left HBounded1 HHeap1 HV1 | |];
    subst; clear HLeft.
  inversion HRight as
    [| | store2 heap2 v_right ty_right HBounded2 HHeap2 HV2 | |];
    subst; clear HRight.
  eapply NNAS_Return; eauto.
  eapply NSRVS_Pair; eauto.
Qed.

Lemma NNoAllocStateShape_pair_par_done_fail_preservation :
  forall store heap v1 v2 phi_left phi_right k ty_out,
    NNoAllocStateShape store
      (StPairParRun
        (StDone heap v1)
        (StDone heap v2)
        phi_left phi_right k)
      ty_out ->
    NNoAllocStateShape store (StError heap) ty_out.
Proof.
  intros store heap v1 v2 phi_left phi_right k ty_out HState.
  inversion HState as
    [| | | |
      store0 left_state right_state phi_left0 phi_right0 k0 heap0
      ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
    subst; clear HState; simpl in *; subst.
  inversion HLeft; subst.
  eapply NNAS_Error; eauto.
Qed.

Lemma NNoAllocStateShape_cond_eval_preservation :
  forall store heap env rho e et ef k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (ECond e et ef) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e (KCond et ef env rho k))
      ty_out.
Proof.
  intros store heap env rho e et ef k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho eff_e0 (static_union eff_t0 eff_f0) eff_res
      HResolveEff HNoAlloc)
    as (eff_e_res & eff_tail_res & HEqEff & HResolveE &
      HNoAllocE & HResolveTail & HNoAllocTail).
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho eff_t0 eff_f0 eff_tail_res
      HResolveTail HNoAllocTail)
    as (eff_t_res & eff_f_res & _HEqTail & HResolveT &
      HNoAllocT & HResolveF & HNoAllocF).
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyBool) (ty_res := TyBool)
    (eff := eff_e0) (eff_res := eff_e_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | exact HEnv]].
  - exact HRho.
  - constructor.
  - assumption.
  - exact HResolveE.
  - exact HNoAllocE.
  - eapply NNAKS_Cond with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_res)
      (eff_t := eff_t0) (eff_f := eff_f0);
    eauto.
Qed.

Lemma NNoAllocStateShape_plus_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EPlus e1 e2) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e1 (KPlusL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  inversion HResolve; subst.
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho eff0 eff3 eff_res HResolveEff HNoAlloc)
    as (eff1_res & eff2_res & _HEq & HResolve1 &
      HNoAlloc1 & HResolve2 & HNoAlloc2).
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat)
    (eff := eff0) (eff_res := eff1_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | exact HEnv]].
  - exact HRho.
  - constructor.
  - assumption.
  - exact HResolve1.
  - exact HNoAlloc1.
  - eapply NNAKS_PlusL; eauto.
Qed.

Lemma NNoAllocStateShape_minus_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EMinus e1 e2) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e1 (KMinusL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  inversion HResolve; subst.
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho eff0 eff3 eff_res HResolveEff HNoAlloc)
    as (eff1_res & eff2_res & _HEq & HResolve1 &
      HNoAlloc1 & HResolve2 & HNoAlloc2).
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat)
    (eff := eff0) (eff_res := eff1_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | exact HEnv]].
  - exact HRho.
  - constructor.
  - assumption.
  - exact HResolve1.
  - exact HNoAlloc1.
  - eapply NNAKS_MinusL; eauto.
Qed.

Lemma NNoAllocStateShape_times_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (ETimes e1 e2) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e1 (KTimesL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  inversion HResolve; subst.
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho eff0 eff3 eff_res HResolveEff HNoAlloc)
    as (eff1_res & eff2_res & _HEq & HResolve1 &
      HNoAlloc1 & HResolve2 & HNoAlloc2).
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat)
    (eff := eff0) (eff_res := eff1_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | exact HEnv]].
  - exact HRho.
  - constructor.
  - assumption.
  - exact HResolve1.
  - exact HNoAlloc1.
  - eapply NNAKS_TimesL; eauto.
Qed.

Lemma NNoAllocStateShape_eq_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EEq e1 e2) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e1 (KEqL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  inversion HResolve; subst.
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho eff0 eff3 eff_res HResolveEff HNoAlloc)
    as (eff1_res & eff2_res & _HEq & HResolve1 &
      HNoAlloc1 & HResolve2 & HNoAlloc2).
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyNat) (ty_res := TyNat)
    (eff := eff0) (eff_res := eff1_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | exact HEnv]].
  - exact HRho.
  - constructor.
  - assumption.
  - exact HResolve1.
  - exact HNoAlloc1.
  - eapply NNAKS_EqL; eauto.
Qed.

Lemma NNoAllocStateShape_concat_eval_preservation :
  forall store heap env rho e1 e2 k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EConcat e1 e2) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e1 (KConcatL e2 env rho k))
      ty_out.
Proof.
  intros store heap env rho e1 e2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  inversion HResolve; subst.
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho eff0 eff3 eff_res HResolveEff HNoAlloc)
    as (eff1_res & eff2_res & _HEq & HResolve1 &
      HNoAlloc1 & HResolve2 & HNoAlloc2).
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect)
    (eff := eff0) (eff_res := eff1_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | exact HEnv]].
  - exact HRho.
  - constructor.
  - assumption.
  - exact HResolve1.
  - exact HNoAlloc1.
  - eapply NNAKS_ConcatL; eauto.
Qed.

Lemma NNoAllocStateShape_ref_eval_impossible :
  forall store heap env rho r e r_val k ty_out,
    eval_region rho r = Some r_val ->
    NNoAllocStateShape store
      (StEval heap env rho (ERef r e) k)
      ty_out ->
    False.
Proof.
  intros store heap env rho r e r_val k ty_out HRgn HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  inversion HResolveEff as
    [| rho_res action action_res eff_tail eff_tail_res
      HResolveAction HResolveTail];
    subst.
  inversion HResolveAction; subst.
  eapply static_noalloc_alloc_cons_false; eauto.
Qed.

Lemma NNoAllocStateShape_ref_return_impossible :
  forall store heap v r_val k ty_out,
    NNoAllocStateShape store
      (StReturn heap v (KRef r_val k))
      ty_out ->
    False.
Proof.
  intros store heap v r_val k ty_out HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HK.
Qed.

Lemma NNoAllocStateShape_deref_eval_preservation :
  forall store heap env rho r e k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EDeref r e) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e (KDeref r k))
      ty_out.
Proof.
  intros store heap env rho r e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  inversion HResolveEff as
    [| rho_res action action_res eff_tail eff_tail_res
      HResolveAction HResolveTail];
    subst.
  inversion HResolveAction; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  assert (HNoAllocChild : static_noalloc eff_tail_res).
  {
    eapply static_noalloc_cons_tail; eauto.
  }
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_res)
    (eff := eff0) (eff_res := eff_tail_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | exact HEnv]].
  - exact HRho.
  - eapply NResolve_Ref; eauto.
    eapply NResolveRegionType_region_expr_to_type.
    exact HRgn.
  - assumption.
  - assumption.
  - exact HNoAllocChild.
  - eapply NNAKS_Deref; eauto.
Qed.

Lemma NNoAllocStateShape_assign_eval_preservation :
  forall store heap env rho r ea ev k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EAssign r ea ev) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho ea (KAssignLoc r ev env rho k))
      ty_out.
Proof.
  intros store heap env rho r ea ev k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  try normalize_resolved_effect HResolveEff.
  inversion HResolveEff as
    [| rho_res action action_res eff_tail eff_tail_res
      HResolveAction HResolveTail];
    subst.
  inversion HResolveAction; subst.
  match goal with
  | HWF : region_expr_wf omega r |- _ =>
      destruct (NRhoModels_eval_region omega rho r HRho HWF)
        as (r_val & HRgn)
  end.
  match goal with
  | HCheckedVal : NCheckedTcExp gamma omega ev ty eff_v0 |- _ =>
      pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HCheckedVal)
        as HTyCellWF
  end.
  destruct
    (NResolveTy_exists 0 omega rho ty HRho HTyCellWF)
    as (ty_cell_res & HTyResolve).
  assert (HNoAllocTail : static_noalloc eff_tail_res).
  {
    eapply static_noalloc_cons_tail; eauto.
  }
  rewrite <- H5 in HResolveTail.
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho eff_a0 eff_v0 eff_tail_res HResolveTail HNoAllocTail)
    as (eff_a_res & eff_v_res & _HEq & HResolveA &
      HNoAllocA & HResolveV & HNoAllocV).
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyRef (region_expr_to_type r) ty)
    (ty_res := TyRef (region_const_type r_val) ty_cell_res)
    (eff := eff_a0) (eff_res := eff_a_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | exact HEnv]].
  - exact HRho.
  - eapply NResolve_Ref; eauto.
    eapply NResolveRegionType_region_expr_to_type.
    exact HRgn.
  - assumption.
  - exact HResolveA.
  - exact HNoAllocA.
  - eapply NNAKS_AssignLoc with
      (gamma := gamma) (omega := omega)
      (ty := ty) (ty_res := ty_cell_res)
      (eff_v := eff_v0);
    eauto.
Qed.

Lemma NNoAllocStateShape_read_conc_eval_preservation :
  forall store heap env rho e k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EReadConc e) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e (KReadConc k))
      ty_out.
Proof.
  intros store heap env rho e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  inversion HResolve; subst.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H3) as HRefWF.
  inversion HRefWF; subst.
  match goal with
  | HRgnWF : NRegionTypeWFAt 0 omega r0,
    HTyWF : NTyWFAt 0 omega ty |- _ =>
      destruct
        (NResolveRegionType_exists 0 omega rho r0 HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (NResolveTy_exists 0 omega rho ty HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (NResolveRegionType_wf0_const
          omega rho r0 rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply NNAS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef r0 ty)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff) (eff_res := eff_res);
      [ unfold NStoreResolvedRuntimeShape;
        split; [exact HBounded | split; [exact HHeap | exact HEnv]]
      | exact HRho
      | eapply NResolve_Ref; eauto
      | eauto
      | exact HResolveEff
      | exact HNoAlloc
      | eapply NNAKS_ReadConc; eauto ]
  end.
Qed.

Lemma NNoAllocStateShape_write_conc_eval_preservation :
  forall store heap env rho e k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EWriteConc e) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho e (KWriteConc k))
      ty_out.
Proof.
  intros store heap env rho e k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  inversion HResolve; subst.
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H3) as HRefWF.
  inversion HRefWF; subst.
  match goal with
  | HRgnWF : NRegionTypeWFAt 0 omega r0,
    HTyWF : NTyWFAt 0 omega ty |- _ =>
      destruct
        (NResolveRegionType_exists 0 omega rho r0 HRho HRgnWF)
        as (rgn_res & HRgnResolve);
      destruct (NResolveTy_exists 0 omega rho ty HRho HTyWF)
        as (ty_ref_res & HTyResolve);
      destruct
        (NResolveRegionType_wf0_const
          omega rho r0 rgn_res HRgnWF HRgnResolve)
        as (r_val & HRgnResEq);
      subst rgn_res;
      eapply NNAS_Eval with
        (gamma := gamma) (omega := omega)
        (ty := TyRef r0 ty)
        (ty_res := TyRef (region_const_type r_val) ty_ref_res)
        (eff := eff) (eff_res := eff_res);
      [ unfold NStoreResolvedRuntimeShape;
        split; [exact HBounded | split; [exact HHeap | exact HEnv]]
      | exact HRho
      | eapply NResolve_Ref; eauto
      | eauto
      | exact HResolveEff
      | exact HNoAlloc
      | eapply NNAKS_WriteConc; eauto ]
  end.
Qed.

Lemma NNoAllocStateShape_mu_app_eval_preservation :
  forall store heap env rho ef ea k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EMuApp ef ea) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho ef (KMuAppFun ea env rho k))
      ty_out.
Proof.
  intros store heap env rho ef ea k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  match goal with
  | HFunChecked : NCheckedTcExp gamma omega ef
      (TyArrow ?ty_arg0 ?eff_body0 ?ty_body0 ?eff_summary0) ?eff_f0 |- _ =>
      pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HFunChecked)
        as HFunWF;
      inversion HFunWF; subst;
      match goal with
      | HArgWF : NTyWFAt 0 omega ty_arg0,
        HBodyEffWF : NStaticEffectWFAt 0 omega eff_body0,
        HSummaryEffWF : NStaticEffectWFAt 0 omega eff_summary0 |- _ =>
          destruct (NResolveTy_exists 0 omega rho ty_arg0 HRho HArgWF)
            as (ty_arg_res & HArgResolve);
          destruct
            (NResolveStaticEffect_exists
              0 omega rho eff_body0 HRho HBodyEffWF)
            as (eff_body_res & HBodyEffResolve);
          destruct
            (NResolveStaticEffect_exists
              0 omega rho eff_summary0 HRho HSummaryEffWF)
            as (eff_summary_res & HSummaryEffResolve);
          destruct
            (NResolveStaticEffect_static_noalloc_union_inv
              rho eff_f0 (static_union eff_a0 eff_body0)
              eff_res HResolveEff HNoAlloc)
            as (eff_f_res & eff_tail_res & _HEq &
              HResolveF & HNoAllocF & HResolveTail & HNoAllocTail);
          destruct
            (NResolveStaticEffect_static_noalloc_union_inv
              rho eff_a0 eff_body0 eff_tail_res
              HResolveTail HNoAllocTail)
            as (eff_a_res & eff_body_res_noalloc & _HEqTail &
              HResolveA & HNoAllocA & HResolveBodyNoAlloc &
              HNoAllocBody);
          pose proof
            (NResolveStaticEffect_deterministic
              rho eff_body0 eff_body_res eff_body_res_noalloc
              HBodyEffResolve HResolveBodyNoAlloc)
            as HBodyEq;
          subst eff_body_res_noalloc;
          eapply NNAS_Eval with
            (gamma := gamma) (omega := omega)
            (ty := TyArrow ty_arg0 eff_body0 ty_body0 eff_summary0)
            (ty_res := TyArrow
              ty_arg_res eff_body_res ty_res eff_summary_res)
            (eff := eff_f0) (eff_res := eff_f_res);
          [ unfold NStoreResolvedRuntimeShape;
            split; [exact HBounded | split; [exact HHeap | exact HEnv]]
          | exact HRho
          | eapply NResolve_Arrow; eauto
          | exact HFunChecked
          | exact HResolveF
          | exact HNoAllocF
          | eapply NNAKS_MuAppFun with
              (gamma := gamma) (omega := omega)
              (ty_arg := ty_arg0) (ty_body := ty_body0)
              (eff_body := eff_body0)
              (eff_summary := eff_summary0)
              (eff_arg := eff_a0);
            eauto ]
      end
  end.
Qed.

Lemma NNoAllocStateShape_eff_app_eval_preservation :
  forall store heap env rho ef ea k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (EEffApp ef ea) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho ef (KEffAppFun ea env rho k))
      ty_out.
Proof.
  intros store heap env rho ef ea k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  inversion HResolve; subst.
  try normalize_resolved_effect HResolveEff.
  match goal with
  | HFunChecked : NCheckedTcExp gamma omega ef
      (TyArrow ?ty_arg0 ?eff_body0 ?ty_body0 ?eff_summary0) ?eff_f0 |- _ =>
      pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ HFunChecked)
        as HFunWF;
      inversion HFunWF; subst;
      match goal with
      | HArgWF : NTyWFAt 0 omega ty_arg0,
        HBodyEffWF : NStaticEffectWFAt 0 omega eff_body0,
        HBodyWF : NTyWFAt 0 omega ty_body0,
        HSummaryEffWF : NStaticEffectWFAt 0 omega eff_summary0 |- _ =>
          destruct (NResolveTy_exists 0 omega rho ty_arg0 HRho HArgWF)
            as (ty_arg_res & HArgResolve);
          destruct
            (NResolveStaticEffect_exists
              0 omega rho eff_body0 HRho HBodyEffWF)
            as (eff_body_res & HBodyEffResolve);
          destruct (NResolveTy_exists 0 omega rho ty_body0 HRho HBodyWF)
            as (ty_body_res & HBodyResolve);
          destruct
            (NResolveStaticEffect_exists
              0 omega rho eff_summary0 HRho HSummaryEffWF)
            as (eff_summary_res & HSummaryEffResolve);
          destruct
            (NResolveStaticEffect_static_noalloc_union_inv
              rho eff_f0 (static_union eff_a0 eff_summary0)
              eff_res HResolveEff HNoAlloc)
            as (eff_f_res & eff_tail_res & _HEq &
              HResolveF & HNoAllocF & HResolveTail & HNoAllocTail);
          destruct
            (NResolveStaticEffect_static_noalloc_union_inv
              rho eff_a0 eff_summary0 eff_tail_res
              HResolveTail HNoAllocTail)
            as (eff_a_res & eff_summary_res_noalloc & _HEqTail &
              HResolveA & HNoAllocA & HResolveSummaryNoAlloc &
              HNoAllocSummary);
          pose proof
            (NResolveStaticEffect_deterministic
              rho eff_summary0 eff_summary_res eff_summary_res_noalloc
              HSummaryEffResolve HResolveSummaryNoAlloc)
            as HSummaryEq;
          subst eff_summary_res_noalloc;
          eapply NNAS_Eval with
            (gamma := gamma) (omega := omega)
            (ty := TyArrow ty_arg0 eff_body0 ty_body0 eff_summary0)
            (ty_res := TyArrow
              ty_arg_res eff_body_res ty_body_res eff_summary_res)
            (eff := eff_f0) (eff_res := eff_f_res);
          [ unfold NStoreResolvedRuntimeShape;
            split; [exact HBounded | split; [exact HHeap | exact HEnv]]
          | exact HRho
          | eapply NResolve_Arrow; eauto
          | exact HFunChecked
          | exact HResolveF
          | exact HNoAllocF
          | eapply NNAKS_EffAppFun with
              (gamma := gamma) (omega := omega)
              (ty_arg := ty_arg0) (ty_body := ty_body0)
              (eff_body := eff_body0)
              (eff_summary := eff_summary0)
              (eff_arg := eff_a0);
            eauto ]
      end
  end.
Qed.

Lemma NNoAllocStateShape_pair_par_eval_preservation :
  forall store heap env rho ef1 ea1 ef2 ea2 k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho
        (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho (EEffApp ef1 ea1)
        (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
      ty_out.
Proof.
  intros store heap env rho ef1 ea1 ef2 ea2 k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  try rewrite <- H11 in HResolveEff.
  destruct
    (NResolveTy_exists
      0 omega rho ty1 HRho
      (NCheckedTcExp_ty_wf _ _ _ _ _ H12))
    as (ty1_res & HResolveTy1).
  destruct
    (NResolveTy_exists
      0 omega rho ty2 HRho
      (NCheckedTcExp_ty_wf _ _ _ _ _ H13))
    as (ty2_res & HResolveTy2).
  pose proof
    (NResolveTy_deterministic
      rho (TyPair ty1 ty2) ty_res
      (TyPair ty1_res ty2_res)
      HResolve
      (NResolve_Pair rho ty1 ty1_res ty2 ty2_res
        HResolveTy1 HResolveTy2))
    as HTyEq.
  subst ty_res.
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho
      (static_union eff_summary0 eff_summary3)
      (static_union eff0 eff3)
      eff_res HResolveEff HNoAlloc)
    as (eff_summary_res & eff_run_res & _HEq &
      HResolveSummary & HNoAllocSummary &
      HResolveRun & HNoAllocRun).
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho eff_summary0 eff_summary3
      eff_summary_res HResolveSummary HNoAllocSummary)
    as (eff_summary1_res & eff_summary2_res & _HEqSummary &
      HResolveSummary1 & HNoAllocSummary1 &
      HResolveSummary2 & HNoAllocSummary2).
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho eff0 eff3
      eff_run_res HResolveRun HNoAllocRun)
    as (eff1_res & eff2_res & _HEqRun &
      HResolveRun1 & HNoAllocRun1 &
      HResolveRun2 & HNoAllocRun2).
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyEffect) (ty_res := TyEffect)
    (eff := eff_summary0) (eff_res := eff_summary1_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | exact HEnv]].
  - exact HRho.
  - constructor.
  - exact H14.
  - exact HResolveSummary1.
  - exact HNoAllocSummary1.
  - eapply NNAKS_PairParEff1 with
      (gamma := gamma) (omega := omega)
      (ty1 := ty1) (ty2 := ty2)
      (eff1 := eff0) (eff2 := eff3)
      (eff_summary2 := eff_summary3);
    eauto.
Qed.

Lemma NNoAllocStateShape_rgn_app_eval_preservation :
  forall store heap env rho er r k ty_out,
    NNoAllocStateShape store
      (StEval heap env rho (ERgnApp er r) k)
      ty_out ->
    NNoAllocStateShape store
      (StEval heap env rho er (KRgnApp r rho k))
      ty_out.
Proof.
  intros store heap env rho er r k ty_out HState.
  inversion HState as
    [store0 heap0 env0 rho0 e0 k0 gamma omega ty_result ty_res
      eff eff_res ty_out0 HRuntime HRho HResolve HChecked
      HResolveEff HNoAlloc HK | | | |];
    subst; clear HState.
  destruct HRuntime as (HBounded & HHeap & HEnv).
  pose proof (NCheckedTcExp_to_NTcExp _ _ _ _ _ HChecked) as HTyped.
  pose proof (NCheckedTcExp_shape _ _ _ _ _ HChecked) as HShape.
  inversion HTyped; subst.
  inversion HShape; subst.
  try normalize_resolved_effect HResolveEff.
  try rewrite <- H5 in HResolveEff.
  destruct (NRhoModels_eval_region omega rho r HRho H7)
    as (r_val & HRgn).
  pose proof (NCheckedTcExp_ty_wf _ _ _ _ _ H8) as HFunWF.
  inversion HFunWF; subst.
  destruct
    (NResolveStaticEffect_exists 1 omega rho eff_body0 HRho H9)
    as (eff_body_res & HEffResolve).
  destruct
    (NResolveTy_exists 1 omega rho ty0 HRho H10)
    as (ty_body_res & HTyResolve).
  pose proof
    (NResolveTy_open_ty
      rho r ty0 ty_body_res r_val HRgn HTyResolve)
    as HOpenResolve.
  rewrite H4 in HOpenResolve.
  pose proof
    (NResolveTy_deterministic
      rho (open_ty r ty) ty_res
      (open_ty_type (region_const_type r_val) ty_body_res)
      HResolve HOpenResolve)
    as HTyResEq.
  subst ty_res.
  destruct
    (NResolveStaticEffect_static_noalloc_union_inv
      rho eff_f0 (open_static_effect r eff_body0)
      eff_res HResolveEff HNoAlloc)
    as (eff_f_res & eff_open_res & _HEq &
      HResolveF & HNoAllocF & HResolveOpen & HNoAllocOpen).
  pose proof
    (NResolveStaticEffect_open_static_effect
      rho r eff_body0 eff_body_res r_val HRgn HEffResolve)
    as HOpenEffResolve.
  pose proof
    (NResolveStaticEffect_deterministic
      rho (open_static_effect r eff_body0)
      eff_open_res
      (open_static_effect_type
        (region_const_type r_val) eff_body_res)
      HResolveOpen HOpenEffResolve)
    as HOpenEffEq.
  subst eff_open_res.
  eapply NNAS_Eval with
    (gamma := gamma) (omega := omega)
    (ty := TyForallRgn eff_body0 ty0)
    (ty_res := TyForallRgn eff_body_res ty_body_res)
    (eff := eff_f0) (eff_res := eff_f_res).
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | exact HEnv]].
  - exact HRho.
  - eapply NResolve_ForallRgn; eauto.
  - exact H8.
  - exact HResolveF.
  - exact HNoAllocF.
  - eapply NNAKS_RgnApp; eauto.
Qed.

Lemma NNoAllocStateShape_rgn_app_return_preservation :
  forall store heap closure_env closure_rho x e arg_rho r r_val k ty_out,
    eval_region arg_rho r = Some r_val ->
    NNoAllocStateShape store
      (StReturn heap
        (VRegionClosure closure_env closure_rho x e)
        (KRgnApp r arg_rho k))
      ty_out ->
    NNoAllocStateShape store
      (StEval heap closure_env
        (rho_extend x r_val closure_rho)
        e
        k)
      ty_out.
Proof.
  intros store heap closure_env closure_rho x e arg_rho r r_val k ty_out
    HRgn HState.
  inversion HState as
    [| store0 heap0 v0 k0 ty_in ty_out0
      HBounded HHeap HV HK | | |];
    subst; clear HState.
  inversion HV; subst.
  inversion HK; subst.
  match goal with
  | HRgnKont : eval_region arg_rho r = Some ?r_val0 |- _ =>
      rewrite HRgn in HRgnKont;
      inversion HRgnKont; subst; clear HRgnKont
  end.
  match goal with
  | |- NNoAllocStateShape _
      (StEval _ _ (rho_extend _ ?r_open _) _ _) _ =>
      eapply NNAS_Eval with
        (gamma := gamma) (omega := x :: omega)
        (ty := ty)
        (ty_res := open_ty_type (region_const_type r_open) ty_res)
        (eff := eff)
        (eff_res := open_static_effect_type
          (region_const_type r_open) eff_res)
  end.
  - unfold NStoreResolvedRuntimeShape.
    split; [exact HBounded | split; [exact HHeap | ]].
    eapply NStoreResolvedEnvShape_extend_fresh;
      eauto using
        NCheckedRegionBody_fresh,
        NCheckedRegionBody_ctx_wf.
  - eapply NRhoModels_extend; eauto.
  - eapply NResolveTy_rho_extend_close_ty.
    + exact
        (NCheckedTcExp_ty_wf
          _ _ _ _ _
          (NCheckedRegionBody_checked _ _ _ _ _ _ H9)).
    + eauto.
  - exact (NCheckedRegionBody_checked _ _ _ _ _ _ H9).
  - unfold close_static_effect, open_static_effect_type.
    eapply NResolveStaticEffect_rho_extend_close_static_effect_at.
    + exact
        (NCheckedTcExp_eff_wf
          _ _ _ _ _
          (NCheckedRegionBody_checked _ _ _ _ _ _ H9)).
    + exact H7.
  - assumption.
  - assumption.
Qed.

Lemma NNoAllocStateShape_step_preservation :
  forall state label state' store ty,
    NStep state label state' ->
    NNoAllocStateShape store state ty ->
    NoAllocTrace (label_trace label) /\
    NNoAllocStateShape store state' ty /\
    NNoAllocStepTransport store state state'.
Proof.
  intros state label state' store ty HStep.
  revert store ty.
  induction HStep; intros store ty HState;
    try solve
      [ split; [apply NoAllocTrace_label_silent |];
        split;
        [ eauto using
            NNoAllocStateShape_const_preservation,
            NNoAllocStateShape_bool_preservation,
            NNoAllocStateShape_var_preservation,
            NNoAllocStateShape_mu_preservation,
            NNoAllocStateShape_lambda_rgn_preservation,
            NNoAllocStateShape_empty_preservation,
            NNoAllocStateShape_top_preservation,
            NNoAllocStateShape_alloc_abs_preservation,
            NNoAllocStateShape_read_abs_preservation,
            NNoAllocStateShape_write_abs_preservation,
            NNoAllocStateShape_read_conc_preservation,
            NNoAllocStateShape_write_conc_preservation,
            NNoAllocStateShape_done_preservation,
            NNoAllocStateShape_cond_true_preservation,
            NNoAllocStateShape_cond_false_preservation,
            NNoAllocStateShape_deref_preservation,
            NNoAllocStateShape_assign_loc_preservation,
            NNoAllocStateShape_plus_l_preservation,
            NNoAllocStateShape_plus_r_preservation,
            NNoAllocStateShape_minus_l_preservation,
            NNoAllocStateShape_minus_r_preservation,
            NNoAllocStateShape_times_l_preservation,
            NNoAllocStateShape_times_r_preservation,
            NNoAllocStateShape_eq_l_preservation,
            NNoAllocStateShape_eq_r_preservation,
            NNoAllocStateShape_concat_l_preservation,
            NNoAllocStateShape_concat_r_preservation,
            NNoAllocStateShape_mu_app_eval_arg_preservation,
            NNoAllocStateShape_eff_app_eval_arg_preservation,
            NNoAllocStateShape_mu_app_body_preservation,
            NNoAllocStateShape_eff_app_body_preservation,
            NNoAllocStateShape_pair_par_eff1_preservation,
            NNoAllocStateShape_pair_par_check_pass_preservation,
            NNoAllocStateShape_pair_par_check_fail_preservation,
            NNoAllocStateShape_pair_par_left_error_preservation,
            NNoAllocStateShape_pair_par_right_error_preservation,
            NNoAllocStateShape_pair_par_done_pass_preservation,
            NNoAllocStateShape_pair_par_done_fail_preservation,
            NNoAllocStateShape_cond_eval_preservation,
            NNoAllocStateShape_plus_eval_preservation,
            NNoAllocStateShape_minus_eval_preservation,
            NNoAllocStateShape_times_eval_preservation,
            NNoAllocStateShape_eq_eval_preservation,
            NNoAllocStateShape_concat_eval_preservation,
            NNoAllocStateShape_deref_eval_preservation,
            NNoAllocStateShape_assign_eval_preservation,
            NNoAllocStateShape_read_conc_eval_preservation,
            NNoAllocStateShape_write_conc_eval_preservation,
            NNoAllocStateShape_mu_app_eval_preservation,
            NNoAllocStateShape_eff_app_eval_preservation,
            NNoAllocStateShape_pair_par_eval_preservation,
            NNoAllocStateShape_rgn_app_eval_preservation,
            NNoAllocStateShape_rgn_app_return_preservation
        | apply NNoAllocStepTransport_same; reflexivity ] ];
    try solve
      [ split; [apply NoAllocTrace_label_read |];
        split;
        [ eauto using NNoAllocStateShape_deref_preservation
        | apply NNoAllocStepTransport_same; reflexivity ] ];
    try solve
      [ split; [apply NoAllocTrace_label_write |];
        destruct
          (NNoAllocStateShape_assign_val_preservation
            _ _ _ _ _ _ _ _ HState)
          as (HState' & HTransport);
        split; [exact HState' | exact HTransport] ];
    try solve
      [ exfalso; eauto using
          NNoAllocStateShape_ref_eval_impossible,
          NNoAllocStateShape_ref_return_impossible ].
  - inversion HState as
      [| | | |
        store0 left_state0 right_state0 phi_left0 phi_right0 k0 heap
        ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
      subst; clear HState.
    destruct (IHHStep store ty1 HLeft) as
      (HNoAlloc & HLeft' & HTransport).
    split; [exact HNoAlloc |].
    split.
    + eapply NNAS_PairParRun with
        (heap := state_heap left_state') (ty1 := ty1) (ty2 := ty2).
      * reflexivity.
      * rewrite state_heap_with_state_heap. reflexivity.
      * exact HLeft'.
      * eapply HTransport.
        -- exact HHeapRight.
        -- exact HRight.
      * exact HK.
    + intros sibling ty_s HSiblingHeap HSibling.
      eapply HTransport.
      * exact HSiblingHeap.
      * exact HSibling.
  - inversion HState as
      [| | | |
        store0 left_state right_state0 phi_left0 phi_right0 k0 heap0
        ty1 ty2 ty_out0 HHeapLeft HHeapRight HLeft HRight HK];
      subst; clear HState.
    destruct (IHHStep store ty2 HRight) as
      (HNoAlloc & HRight' & HTransport).
    split; [exact HNoAlloc |].
    split.
    + eapply NNAS_PairParRun with
        (heap := state_heap right_state') (ty1 := ty1) (ty2 := ty2).
      * rewrite state_heap_with_state_heap. reflexivity.
      * reflexivity.
      * eapply HTransport.
        -- simpl. rewrite HHeapRight. reflexivity.
        -- exact HLeft.
      * exact HRight'.
      * exact HK.
    + intros sibling ty_s HSiblingHeap HSibling.
      eapply HTransport.
      * rewrite HHeapRight.
        exact HSiblingHeap.
      * exact HSibling.
  - split; [apply NoAllocTrace_label_silent |].
    split.
    + eapply NNoAllocStateShape_pair_par_right_error_preservation;
        eauto.
    + intros sibling ty_s HSiblingHeap HSibling.
      eapply NNoAllocStateShape_with_state_heap_same; eauto.
      inversion HState; subst; simpl in *; congruence.
Qed.
