From stdpp Require Import gmap.
From Stdlib Require Import Ascii.
From Stdlib Require Import Program.Equality.

Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Runtime.SmallStepFacts.
Require Import theories.Runtime.SmallStepTyping.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.
Require Import theories.Core.StaticActions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.
Require Import theories.Meta.MapFacts.
Require Import theories.Meta.RegionSubstitutionFacts.
Require Import theories.Meta.TypingWeakeningFacts.

Definition SequentialHead (e : Expr) : Prop :=
  match e with
  | Pair_Par _ _ _ _ => False
  | _ => True
  end.

Definition EvalHeadRegionsResolved (rho : Rho) (e : Expr) : Prop :=
  match e with
  | AllocAbs w => exists r, find_R w rho = Some r
  | ReadAbs w => exists r, find_R w rho = Some r
  | WriteAbs w => exists r, find_R w rho = Some r
  | _ => True
  end.

Inductive RuntimeValShape : Sigma -> Tau -> Val -> Prop :=
| RVS_Natural :
    forall stty n,
      RuntimeValShape stty Ty_Natural (Num n)
| RVS_Boolean :
    forall stty b,
      RuntimeValShape stty Ty_Boolean (Bit b)
| RVS_Arrow :
    forall stty env rho f x ec ee rgns ctxt tya effc tyc effe,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      (forall y v t,
          find_E y env = Some v ->
          find_T y ctxt = Some t ->
          RuntimeValShape stty (subst_rho rho t) v) ->
      TcExp
        (ctxt, rgns, Mu f x ec ee,
          Ty_Arrow tya effc tyc effe Ty_Effect, Empty_Static_Action) ->
      RuntimeValShape
        stty
        (subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect))
        (Cls (env, rho, Mu f x ec ee))
| RVS_ForallRgn :
    forall stty env rho x eb rgns ctxt effr tyr,
      TcRho (rho, rgns) ->
      TcInc (ctxt, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      (forall y v t,
          find_E y env = Some v ->
          find_T y ctxt = Some t ->
          RuntimeValShape stty (subst_rho rho t) v) ->
      TcExp
        (ctxt, rgns, Lambda x eb,
          Ty_ForallRgn effr tyr, Empty_Static_Action) ->
      RuntimeValShape
        stty
        (subst_rho rho (Ty_ForallRgn effr tyr))
        (Cls (env, rho, Lambda x eb))
| RVS_Ref :
    forall stty s l t,
      RuntimeValShape
        stty
        (Ty_Ref (Rgn_Const true true s) t)
        (Loc (Rgn_Const true false s) l)
| RVS_Unit :
    forall stty,
      RuntimeValShape stty Ty_Unit Unit
| RVS_Pair :
    forall stty v1 v2 t1 t2,
      RuntimeValShape stty t1 v1 ->
      RuntimeValShape stty t2 v2 ->
      RuntimeValShape stty (Ty_Pair t1 t2) (Pair (v1, v2))
| RVS_Effect :
    forall stty theta,
      RuntimeValShape stty Ty_Effect (Eff theta).

Definition RuntimeEnvShape
    (stty : Sigma) (rho : Rho) (env : Env) (ctxt : Gamma) : Prop :=
  forall x v t,
    find_E x env = Some v ->
    find_T x ctxt = Some t ->
    RuntimeValShape stty (subst_rho rho t) v.

Ltac discriminate_subst_rho_shape :=
  match goal with
  | H : _ = subst_rho _ (Ty_Arrow _ _ _ _ _) |- _ =>
      rewrite subst_rho_arrow in H; discriminate
  | H : subst_rho _ (Ty_Arrow _ _ _ _ _) = _ |- _ =>
      rewrite subst_rho_arrow in H; discriminate
  | H : _ = subst_rho _ (Ty_ForallRgn _ _) |- _ =>
      rewrite subst_rho_forallrgn in H; discriminate
  | H : subst_rho _ (Ty_ForallRgn _ _) = _ |- _ =>
      rewrite subst_rho_forallrgn in H; discriminate
  end.

Lemma RuntimeValShape_natural_inv :
  forall stty v,
    RuntimeValShape stty Ty_Natural v ->
    exists n, v = Num n.
Proof.
  intros stty v HShape.
  inversion HShape; subst; eauto; discriminate_subst_rho_shape.
Qed.

Lemma RuntimeValShape_boolean_inv :
  forall stty v,
    RuntimeValShape stty Ty_Boolean v ->
    v = Bit true \/ v = Bit false.
Proof.
  intros stty v HShape.
  inversion HShape; subst; try discriminate_subst_rho_shape.
  destruct b; auto.
Qed.

Lemma RuntimeValShape_arrow_inv :
  forall stty v tya effc tyc effe,
    RuntimeValShape stty (Ty_Arrow tya effc tyc effe Ty_Effect) v ->
    exists env rho f x ec ee,
      v = Cls (env, rho, Mu f x ec ee).
Proof.
  intros stty v tya effc tyc effe HShape.
  inversion HShape; subst; try discriminate; try discriminate_subst_rho_shape.
  repeat eexists.
Qed.

Lemma RuntimeValShape_forall_inv :
  forall stty v effr tyr,
    RuntimeValShape stty (Ty_ForallRgn effr tyr) v ->
    exists env rho x eb,
      v = Cls (env, rho, Lambda x eb).
Proof.
  intros stty v effr tyr HShape.
  inversion HShape; subst; try discriminate; try discriminate_subst_rho_shape.
  repeat eexists.
Qed.

Lemma RuntimeValShape_mu_closure_inv :
  forall stty ty env rho f x ec ee,
    RuntimeValShape stty ty (Cls (env, rho, Mu f x ec ee)) ->
    exists rgns ctxt tya effc tyc effe,
      ty = subst_rho rho (Ty_Arrow tya effc tyc effe Ty_Effect) /\
      TcRho (rho, rgns) /\
      TcInc (ctxt, rgns) /\
      TcEnv (stty, rho, env, ctxt) /\
      RuntimeEnvShape stty rho env ctxt /\
      TcExp
        (ctxt, rgns, Mu f x ec ee,
          Ty_Arrow tya effc tyc effe Ty_Effect, Empty_Static_Action).
Proof.
  intros stty ty env rho f x ec ee HShape.
  dependent destruction HShape; try discriminate.
  exists rgns, ctxt, tya, effc, tyc, effe.
  split; [reflexivity |].
  split; [exact H |].
  split; [exact H0 |].
  split; [exact H1 |].
  split; [unfold RuntimeEnvShape; exact H2 |].
  exact H3.
Qed.

Lemma RuntimeValShape_lambda_closure_inv :
  forall stty ty env rho x eb,
    RuntimeValShape stty ty (Cls (env, rho, Lambda x eb)) ->
    exists rgns ctxt effr tyr,
      ty = subst_rho rho (Ty_ForallRgn effr tyr) /\
      TcRho (rho, rgns) /\
      TcInc (ctxt, rgns) /\
      TcEnv (stty, rho, env, ctxt) /\
      RuntimeEnvShape stty rho env ctxt /\
      TcExp
        (ctxt, rgns, Lambda x eb,
          Ty_ForallRgn effr tyr, Empty_Static_Action).
Proof.
  intros stty ty env rho x eb HShape.
  dependent destruction HShape; try discriminate.
  exists rgns, ctxt, effr, tyr.
  split; [reflexivity |].
  split; [exact H |].
  split; [exact H0 |].
  split; [exact H1 |].
  split; [unfold RuntimeEnvShape; exact H2 |].
  exact H3.
Qed.

Lemma RuntimeValShape_ref_const_inv :
  forall stty v s t,
    RuntimeValShape stty (Ty_Ref (Rgn_Const true true s) t) v ->
    exists l, v = Loc (Rgn_Const true false s) l.
Proof.
  intros stty v s t HShape.
  inversion HShape; subst; try discriminate; try discriminate_subst_rho_shape.
  repeat eexists.
Qed.

Lemma RuntimeValShape_effect_inv :
  forall stty v,
    RuntimeValShape stty Ty_Effect v ->
    exists theta, v = Eff theta.
Proof.
  intros stty v HShape.
  inversion HShape; subst; try discriminate; try discriminate_subst_rho_shape.
  repeat eexists.
Qed.

Lemma RuntimeEnvShape_find :
  forall stty rho env ctxt x v t,
    RuntimeEnvShape stty rho env ctxt ->
    find_E x env = Some v ->
    find_T x ctxt = Some t ->
    RuntimeValShape stty (subst_rho rho t) v.
Proof.
  intros stty rho env ctxt x v t HEnvShape HFindE HFindT.
  eauto.
Qed.

Lemma RuntimeEnvShape_update :
  forall stty rho env ctxt x v t,
    RuntimeEnvShape stty rho env ctxt ->
    RuntimeValShape stty (subst_rho rho t) v ->
    RuntimeEnvShape stty rho (update_E (x, v) env) (update_T (x, t) ctxt).
Proof.
  intros stty rho env ctxt x v t HEnvShape HShape y value ty HFindE HFindT.
  unfold update_E, update_T, find_E, find_T in *; simpl in *.
  destruct (ascii_dec y x) as [Heq | Hneq]; subst.
  - assert (HFindE' : (<[x:=v]> env) !! x = Some v) by apply lookup_insert.
    rewrite HFindE' in HFindE.
    assert (HFindT' : (<[x:=t]> ctxt) !! x = Some t) by apply lookup_insert.
    rewrite HFindT' in HFindT.
    inversion HFindE; inversion HFindT; subst.
    assumption.
  - eapply G_diff_keys_1 in HFindE; eauto.
    eapply G_diff_keys_1 in HFindT; eauto.
Qed.

Lemma RuntimeEnvShape_update_rec :
  forall stty rho env ctxt f vf x vx tf tx,
    RuntimeEnvShape stty rho env ctxt ->
    RuntimeValShape stty (subst_rho rho tf) vf ->
    RuntimeValShape stty (subst_rho rho tx) vx ->
    RuntimeEnvShape stty rho
      (update_rec_E (f, vf) (x, vx) env)
      (update_rec_T (f, tf) (x, tx) ctxt).
Proof.
  intros stty rho env ctxt f vf x vx tf tx HEnvShape HFShape HXShape.
  unfold update_rec_E, update_rec_T.
  apply RuntimeEnvShape_update; auto.
  apply RuntimeEnvShape_update; auto.
Qed.

Lemma RuntimeValShape_store_ext :
  forall stty t v,
    RuntimeValShape stty t v ->
    forall stty',
      (forall k ty,
        find_ST k stty = Some ty ->
        find_ST k stty' = Some ty) ->
      RuntimeValShape stty' t v.
Proof.
  intros stty t v HShape.
  induction HShape; intros stty' HExt.
  - constructor.
  - constructor.
  - eapply RVS_Arrow with (rgns := rgns) (ctxt := ctxt).
    + exact H.
    + exact H0.
    + eapply ext_stores__env; eauto.
    + intros y v0 t0 HFindE HFindT.
      eauto.
    + exact H4.
  - eapply RVS_ForallRgn with (rgns := rgns) (ctxt := ctxt).
    + exact H.
    + exact H0.
    + eapply ext_stores__env; eauto.
    + intros y v0 t0 HFindE HFindT.
      eauto.
    + exact H4.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor.
Qed.

Lemma RuntimeEnvShape_store_ext :
  forall stty rho env ctxt,
    RuntimeEnvShape stty rho env ctxt ->
    forall stty',
      (forall k ty,
        find_ST k stty = Some ty ->
        find_ST k stty' = Some ty) ->
      RuntimeEnvShape stty' rho env ctxt.
Proof.
  intros stty rho env ctxt HEnvShape stty' HExt x v t HFindE HFindT.
  eapply RuntimeValShape_store_ext; eauto.
Qed.

Definition ReturnFrameReady (heap : Heap) (v : Val) (k : Kont) : Prop :=
  match k with
  | KDone => True
  | KMuAppFun _ _ _ _ =>
      exists env' rho' f x ec ee,
        v = Cls (env', rho', Mu f x ec ee)
  | KMuAppArg _ _ _ _ _ _ _ => True
  | KRgnApp w rho _ =>
      exists env' rho' x eb r,
        v = Cls (env', rho', Lambda x eb) /\ find_R w rho = Some r
  | KEffAppFun _ _ _ _ =>
      exists env' rho' f x ec ee,
        v = Cls (env', rho', Mu f x ec ee)
  | KEffAppArg _ _ _ _ _ _ _ => True
  | KPairParEff1 _ _ _ _ _ _ _ =>
      exists theta, v = Eff theta
  | KPairParEff2 _ _ _ _ _ _ theta1 _ =>
      exists theta2,
        v = Eff theta2 /\
        Disjointness theta1 theta2 /\
        ~ Conflictness theta1 theta2
  | KPairParMu1 _ _ _ _ _ => True
  | KPairParMu2 _ _ => True
  | KCond _ _ _ _ _ =>
      v = Bit true \/ v = Bit false
  | KRef w rho _ =>
      exists r, find_R w rho = Some r
  | KDeRef w rho _ =>
      exists l r value,
        v = Loc w l /\ find_R w rho = Some r /\ find_H (r, l) heap = Some value
  | KAssignLoc w _ _ _ _ =>
      exists l, v = Loc w l
  | KAssignVal w l rho _ =>
      exists r, find_R w rho = Some r /\ find_H (r, l) heap <> None
  | KPlusL _ _ _ _ =>
      exists n, v = Num n
  | KPlusR _ _ =>
      exists n, v = Num n
  | KMinusL _ _ _ _ =>
      exists n, v = Num n
  | KMinusR _ _ =>
      exists n, v = Num n
  | KTimesL _ _ _ _ =>
      exists n, v = Num n
  | KTimesR _ _ =>
      exists n, v = Num n
  | KEqL _ _ _ _ =>
      exists n, v = Num n
  | KEqR _ _ =>
      exists n, v = Num n
  | KReadConc _ =>
      exists r l, v = Loc (Rgn_Const true false r) l
  | KWriteConc _ =>
      exists r l, v = Loc (Rgn_Const true false r) l
  | KConcatL _ _ _ _ =>
      exists theta, v = Eff theta
  | KConcatR _ _ =>
      exists theta, v = Eff theta
  end.

Lemma TcRho_TcRgn_find_R :
  forall rho rgns w,
    TcRho (rho, rgns) ->
    TcRgn (rgns, w) ->
    exists r, find_R w rho = Some r.
Proof.
  intros rho rgns w HTcRho HTcRgn.
  inversion HTcRgn; subst; simpl.
  - eauto.
  - inversion HTcRho as [? ? HRho]; subst.
    destruct (HRho r) as [_ HInRho].
    match goal with
    | HSet : set_elem rgns r |- _ => specialize (HInRho HSet)
    end.
    destruct (rho !! r) eqn:HLookup.
    + eauto.
    + exfalso. exact (HInRho HLookup).
Qed.

Lemma TcEnv_find_E :
  forall stty rho env ctxt x t,
    TcEnv (stty, rho, env, ctxt) ->
    find_T x ctxt = Some t ->
    exists v, find_E x env = Some v.
Proof.
  intros stty rho env ctxt x t HTcEnv HFind.
  inversion HTcEnv as [? ? ? ? _ HEnvCtxt _]; subst.
  eauto.
Qed.

Lemma RuntimeEnvShape_var_value :
  forall stty rho env ctxt rgns x t,
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, Var x, t, Empty_Static_Action) ->
    exists v,
      find_E x env = Some v /\
      RuntimeValShape stty (subst_rho rho t) v.
Proof.
  intros stty rho env ctxt rgns x t HTcEnv HEnvShape HTcExp.
  inversion HTcExp; subst.
  match goal with
  | HFindT : find_T x ctxt = Some t |- _ =>
      destruct (TcEnv_find_E stty rho env ctxt x t HTcEnv HFindT)
        as [value HFindE]
  end.
  exists value.
  split; auto.
  eapply RuntimeEnvShape_find; eauto.
Qed.

Lemma TcHeap_find_ST_find_H :
  forall heap stty k t,
    TcHeap (heap, stty) ->
    find_ST k stty = Some t ->
    exists v, find_H k heap = Some v.
Proof.
  intros heap stty k t HTcHeap HFind.
  inversion HTcHeap as [? ? _ HStoreHeap _]; subst.
  eauto.
Qed.

Lemma TcHeap_find_ST_find_H_not_none :
  forall heap stty k t,
    TcHeap (heap, stty) ->
    find_ST k stty = Some t ->
    find_H k heap <> None.
Proof.
  intros heap stty k t HTcHeap HFind HNone.
  destruct (TcHeap_find_ST_find_H heap stty k t HTcHeap HFind)
    as [v HHeap].
  rewrite HNone in HHeap.
  discriminate.
Qed.

Lemma TcVal_loc_find_ST :
  forall stty s l t,
    TcVal
      (stty, Loc (Rgn_Const true false s) l,
        Ty_Ref (Rgn_Const true true s) t) ->
    find_ST (s, l) stty = Some t.
Proof.
  intros stty s l t HTcVal.
  inversion HTcVal; subst; assumption.
Qed.

Lemma return_frame_ready_progress :
  forall heap v k,
    ReturnFrameReady heap v k ->
    CanStep (StReturn heap v k).
Proof.
  intros heap v k HReady.
  destruct k as
    [| ea env rho k
     | env rho f x ec ee k
     | w rho k
     | ea env rho k
     | env rho f x ec ee k
     | ef1 ea1 ef2 ea2 env rho k
     | ef1 ea1 ef2 ea2 env rho theta1 k
     | ef2 ea2 env rho k
     | v1 k
     | et ef env rho k
     | w rho k
     | w rho k
     | w ev env rho k
     | w l rho k
     | e2 env rho k
     | n k
     | e2 env rho k
     | n k
     | e2 env rho k
     | n k
     | e2 env rho k
     | n k
     | k
     | k
     | e2 env rho k
     | theta1 k]; simpl in HReady.
  - exists Silent, (StDone heap v).
    constructor.
  - destruct HReady as (env' & rho' & f & x & ec & ee & HValue).
    subst.
    exists Silent, (StEval heap env rho ea (KMuAppArg env' rho' f x ec ee k)).
    constructor.
  - exists Silent,
      (StEval heap
        (update_rec_E (f, Cls (env, rho, Mu f x ec ee)) (x, v) env)
        rho ec k).
    constructor.
  - destruct HReady as (env' & rho' & x & eb & r & HValue & HFind).
    subst.
    exists Silent, (StEval heap env' (update_R (x, r) rho') eb k).
    now constructor.
  - destruct HReady as (env' & rho' & f & x & ec & ee & HValue).
    subst.
    exists Silent, (StEval heap env rho ea (KEffAppArg env' rho' f x ec ee k)).
    constructor.
  - exists Silent,
      (StEval heap
        (update_rec_E (f, Cls (env, rho, Mu f x ec ee)) (x, v) env)
        rho ee k).
    constructor.
  - destruct HReady as (theta1 & HValue).
    subst.
    exists Silent,
      (StEval heap env rho (Eff_App ef2 ea2)
        (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)).
    constructor.
  - destruct HReady as (theta2 & HValue & HDisj & HNoConf).
    subst.
    exists Silent,
      (StEval heap env rho (Mu_App ef1 ea1)
        (KPairParMu1 ef2 ea2 env rho k)).
    econstructor; eauto.
  - exists Silent,
      (StEval heap env rho (Mu_App ef2 ea2) (KPairParMu2 v k)).
    constructor.
  - exists Silent, (StReturn heap (Pair (v1, v)) k).
    constructor.
  - destruct HReady as [HTrue | HFalse].
    + subst.
      exists Silent, (StEval heap env rho et k).
      constructor.
    + subst.
      exists Silent, (StEval heap env rho ef k).
      constructor.
  - destruct HReady as (r & HFind).
    exists (Act (DA_Alloc r (allocate_H heap r) v)),
      (StReturn
        (update_H ((r, allocate_H heap r), v) heap)
        (Loc (Rgn_Const true false r) (allocate_H heap r))
        k).
    econstructor; eauto.
  - destruct HReady as (l & r & value & HValue & HFindR & HFindH).
    subst.
    exists (Act (DA_Read r l value)), (StReturn heap value k).
    econstructor; eauto.
  - destruct HReady as (l & HValue).
    subst.
    exists Silent, (StEval heap env rho ev (KAssignVal w l rho k)).
    constructor.
  - destruct HReady as (r & HFindR & HFindH).
    exists (Act (DA_Write r l v)),
      (StReturn (update_H ((r, l), v) heap) Unit k).
    econstructor; eauto.
  - destruct HReady as (n & HValue).
    subst.
    exists Silent, (StEval heap env rho e2 (KPlusR n k)).
    constructor.
  - destruct HReady as (n2 & HValue).
    subst.
    exists Silent, (StReturn heap (Num (n + n2)) k).
    constructor.
  - destruct HReady as (n & HValue).
    subst.
    exists Silent, (StEval heap env rho e2 (KMinusR n k)).
    constructor.
  - destruct HReady as (n2 & HValue).
    subst.
    exists Silent, (StReturn heap (Num (n - n2)) k).
    constructor.
  - destruct HReady as (n & HValue).
    subst.
    exists Silent, (StEval heap env rho e2 (KTimesR n k)).
    constructor.
  - destruct HReady as (n2 & HValue).
    subst.
    exists Silent, (StReturn heap (Num (n * n2)) k).
    constructor.
  - destruct HReady as (n & HValue).
    subst.
    exists Silent, (StEval heap env rho e2 (KEqR n k)).
    constructor.
  - destruct HReady as (n2 & HValue).
    subst.
    exists Silent, (StReturn heap (Bit (Nat.eqb n n2)) k).
    constructor.
  - destruct HReady as (r & l & HValue).
    subst.
    exists Silent,
      (StReturn heap (Eff (Some (singleton_set (CA_ReadConc r l)))) k).
    constructor.
  - destruct HReady as (r & l & HValue).
    subst.
    exists Silent,
      (StReturn heap (Eff (Some (singleton_set (CA_WriteConc r l)))) k).
    constructor.
  - destruct HReady as (theta & HValue).
    subst.
    exists Silent, (StEval heap env rho e2 (KConcatR theta k)).
    constructor.
  - destruct HReady as (theta2 & HValue).
    subst.
    exists Silent, (StReturn heap (Eff (Union_Theta theta1 theta2)) k).
    constructor.
Qed.

Lemma WTStateTyped_return_ready_progress :
  forall heap v k tout,
    WTStateTyped (StReturn heap v k) tout ->
    ReturnFrameReady heap v k ->
    CanStep (StReturn heap v k).
Proof.
  intros heap v k tout _ HReady.
  now apply return_frame_ready_progress.
Qed.

Lemma WTStateTyped_return_done_progress :
  forall heap v tout,
    WTStateTyped (StReturn heap v KDone) tout ->
    CanStep (StReturn heap v KDone).
Proof.
  intros heap v tout _.
  apply return_frame_ready_progress.
  simpl. exact I.
Qed.

Lemma WTStateTyped_return_mu_arg_progress :
  forall heap v env rho f x ec ee k tout,
    WTStateTyped (StReturn heap v (KMuAppArg env rho f x ec ee k)) tout ->
    CanStep (StReturn heap v (KMuAppArg env rho f x ec ee k)).
Proof.
  intros heap v env rho f x ec ee k tout _.
  apply return_frame_ready_progress.
  simpl. exact I.
Qed.

Lemma WTStateTyped_return_eff_arg_progress :
  forall heap v env rho f x ec ee k tout,
    WTStateTyped (StReturn heap v (KEffAppArg env rho f x ec ee k)) tout ->
    CanStep (StReturn heap v (KEffAppArg env rho f x ec ee k)).
Proof.
  intros heap v env rho f x ec ee k tout _.
  apply return_frame_ready_progress.
  simpl. exact I.
Qed.

Lemma WTStateTyped_return_ref_progress :
  forall heap v w rho k tout,
    WTStateTyped (StReturn heap v (KRef w rho k)) tout ->
    CanStep (StReturn heap v (KRef w rho k)).
Proof.
  intros heap v w rho k tout HWTState.
  inversion HWTState; subst.
  match goal with
  | HKont : WTKontTyped _ _ _ (KRef w rho k) |- _ =>
      inversion HKont; subst
  end.
  apply return_frame_ready_progress.
  simpl.
  eauto.
Qed.

Lemma WTStateTyped_return_assign_val_progress :
  forall heap v w l rho k tout,
    WTStateTyped (StReturn heap v (KAssignVal w l rho k)) tout ->
    CanStep (StReturn heap v (KAssignVal w l rho k)).
Proof.
  intros heap v w l rho k tout HWTState.
  inversion HWTState; subst.
  match goal with
  | HKont : WTKontTyped _ _ _ (KAssignVal w l rho k) |- _ =>
      inversion HKont; subst
  end.
  apply return_frame_ready_progress.
  simpl.
  match goal with
  | HFindR : find_R w rho = Some ?r,
    HFindST : find_ST (?r, l) ?stty = Some ?t,
    HTcHeap : TcHeap (heap, ?stty) |- _ =>
      exists r; split;
      [ exact HFindR
      | eapply TcHeap_find_ST_find_H_not_none; eauto ]
  end.
Qed.

Lemma WTKontTyped_runtime_shape_ready :
  forall heap stty v tin tout k,
    TcHeap (heap, stty) ->
    TcVal (stty, v, tin) ->
    WTKontTyped stty tin tout k ->
    RuntimeValShape stty tin v ->
    ReturnFrameReady heap v k.
Proof.
  intros heap stty v tin tout k HTcHeap HTcVal HKont HShape.
  revert heap v HTcHeap HTcVal HShape.
  induction HKont; intros heap0 v HTcHeap HTcVal HShape; simpl.
  - exact I.
  - now eapply RuntimeValShape_arrow_inv; eauto.
  - exact I.
  - destruct (RuntimeValShape_forall_inv stty v effr tyr HShape)
      as (env' & rho' & x & eb & HValue).
    destruct (TcRho_TcRgn_find_R rho rgns w H H0) as [r HFind].
    repeat eexists; eauto.
  - now eapply RuntimeValShape_arrow_inv; eauto.
  - exact I.
  - now apply RuntimeValShape_boolean_inv with (stty:=stty).
  - subst. simpl. eauto.
  - subst. simpl in HShape.
    destruct (RuntimeValShape_ref_const_inv stty v s t HShape) as [l HValue].
    subst.
    pose proof (TcVal_loc_find_ST stty s l t HTcVal) as HFindST.
    destruct (TcHeap_find_ST_find_H heap0 stty (s, l) t HTcHeap HFindST)
      as [value HFindH].
    exists l, s, value.
    repeat split; auto.
  - subst. simpl in HShape.
    destruct (RuntimeValShape_ref_const_inv stty v s t HShape) as [l HValue].
    exists l. exact HValue.
  - exists r. split; [assumption |].
    eapply TcHeap_find_ST_find_H_not_none; eauto.
  - now apply RuntimeValShape_natural_inv with (stty:=stty).
  - now apply RuntimeValShape_natural_inv with (stty:=stty).
  - now apply RuntimeValShape_natural_inv with (stty:=stty).
  - now apply RuntimeValShape_natural_inv with (stty:=stty).
  - now apply RuntimeValShape_natural_inv with (stty:=stty).
  - now apply RuntimeValShape_natural_inv with (stty:=stty).
  - now apply RuntimeValShape_natural_inv with (stty:=stty).
  - now apply RuntimeValShape_natural_inv with (stty:=stty).
  - destruct (RuntimeValShape_ref_const_inv stty v r t HShape) as [l HValue].
    exists r, l. exact HValue.
  - destruct (RuntimeValShape_ref_const_inv stty v r t HShape) as [l HValue].
    exists r, l. exact HValue.
  - now apply RuntimeValShape_effect_inv with (stty:=stty).
  - now apply RuntimeValShape_effect_inv with (stty:=stty).
Qed.

Lemma typed_return_runtime_shape_progress :
  forall heap stty v tin tout k,
    TcHeap (heap, stty) ->
    TcVal (stty, v, tin) ->
    WTKontTyped stty tin tout k ->
    RuntimeValShape stty tin v ->
    CanStep (StReturn heap v k).
Proof.
  intros heap stty v tin tout k HTcHeap HTcVal HKont HShape.
  apply return_frame_ready_progress.
  eapply WTKontTyped_runtime_shape_ready; eauto.
Qed.

Lemma return_mu_fun_shape_progress :
  forall heap stty v ea env rho k tya effc tyc effe,
    RuntimeValShape stty (Ty_Arrow tya effc tyc effe Ty_Effect) v ->
    CanStep (StReturn heap v (KMuAppFun ea env rho k)).
Proof.
  intros heap stty v ea env rho k tya effc tyc effe HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_arrow_inv; eauto.
Qed.

Lemma return_eff_fun_shape_progress :
  forall heap stty v ea env rho k tya effc tyc effe,
    RuntimeValShape stty (Ty_Arrow tya effc tyc effe Ty_Effect) v ->
    CanStep (StReturn heap v (KEffAppFun ea env rho k)).
Proof.
  intros heap stty v ea env rho k tya effc tyc effe HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_arrow_inv; eauto.
Qed.

Lemma return_rgn_app_shape_progress :
  forall heap stty v w rho k effr tyr r,
    RuntimeValShape stty (Ty_ForallRgn effr tyr) v ->
    find_R w rho = Some r ->
    CanStep (StReturn heap v (KRgnApp w rho k)).
Proof.
  intros heap stty v w rho k effr tyr r HShape HFind.
  apply return_frame_ready_progress.
  simpl.
  destruct (RuntimeValShape_forall_inv stty v effr tyr HShape)
    as (env' & rho' & x & eb & HValue).
  repeat eexists; eauto.
Qed.

Lemma return_cond_shape_progress :
  forall heap stty v et ef env rho k,
    RuntimeValShape stty Ty_Boolean v ->
    CanStep (StReturn heap v (KCond et ef env rho k)).
Proof.
  intros heap stty v et ef env rho k HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_boolean_inv; eauto.
Qed.

Lemma return_plus_left_shape_progress :
  forall heap stty v e2 env rho k,
    RuntimeValShape stty Ty_Natural v ->
    CanStep (StReturn heap v (KPlusL e2 env rho k)).
Proof.
  intros heap stty v e2 env rho k HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_natural_inv; eauto.
Qed.

Lemma return_plus_right_shape_progress :
  forall heap stty v n k,
    RuntimeValShape stty Ty_Natural v ->
    CanStep (StReturn heap v (KPlusR n k)).
Proof.
  intros heap stty v n k HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_natural_inv; eauto.
Qed.

Lemma return_minus_left_shape_progress :
  forall heap stty v e2 env rho k,
    RuntimeValShape stty Ty_Natural v ->
    CanStep (StReturn heap v (KMinusL e2 env rho k)).
Proof.
  intros heap stty v e2 env rho k HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_natural_inv; eauto.
Qed.

Lemma return_minus_right_shape_progress :
  forall heap stty v n k,
    RuntimeValShape stty Ty_Natural v ->
    CanStep (StReturn heap v (KMinusR n k)).
Proof.
  intros heap stty v n k HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_natural_inv; eauto.
Qed.

Lemma return_times_left_shape_progress :
  forall heap stty v e2 env rho k,
    RuntimeValShape stty Ty_Natural v ->
    CanStep (StReturn heap v (KTimesL e2 env rho k)).
Proof.
  intros heap stty v e2 env rho k HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_natural_inv; eauto.
Qed.

Lemma return_times_right_shape_progress :
  forall heap stty v n k,
    RuntimeValShape stty Ty_Natural v ->
    CanStep (StReturn heap v (KTimesR n k)).
Proof.
  intros heap stty v n k HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_natural_inv; eauto.
Qed.

Lemma return_eq_left_shape_progress :
  forall heap stty v e2 env rho k,
    RuntimeValShape stty Ty_Natural v ->
    CanStep (StReturn heap v (KEqL e2 env rho k)).
Proof.
  intros heap stty v e2 env rho k HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_natural_inv; eauto.
Qed.

Lemma return_eq_right_shape_progress :
  forall heap stty v n k,
    RuntimeValShape stty Ty_Natural v ->
    CanStep (StReturn heap v (KEqR n k)).
Proof.
  intros heap stty v n k HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_natural_inv; eauto.
Qed.

Lemma return_read_conc_shape_progress :
  forall heap stty v k r t,
    RuntimeValShape stty (Ty_Ref (Rgn_Const true true r) t) v ->
    CanStep (StReturn heap v (KReadConc k)).
Proof.
  intros heap stty v k r t HShape.
  apply return_frame_ready_progress.
  simpl.
  destruct (RuntimeValShape_ref_const_inv stty v r t HShape) as [l HValue].
  exists r, l. exact HValue.
Qed.

Lemma return_write_conc_shape_progress :
  forall heap stty v k r t,
    RuntimeValShape stty (Ty_Ref (Rgn_Const true true r) t) v ->
    CanStep (StReturn heap v (KWriteConc k)).
Proof.
  intros heap stty v k r t HShape.
  apply return_frame_ready_progress.
  simpl.
  destruct (RuntimeValShape_ref_const_inv stty v r t HShape) as [l HValue].
  exists r, l. exact HValue.
Qed.

Lemma return_assign_loc_const_shape_progress :
  forall heap stty v s t ev env rho k,
    RuntimeValShape stty (Ty_Ref (Rgn_Const true true s) t) v ->
    CanStep
      (StReturn heap v
        (KAssignLoc (Rgn_Const true false s) ev env rho k)).
Proof.
  intros heap stty v s t ev env rho k HShape.
  apply return_frame_ready_progress.
  simpl.
  destruct (RuntimeValShape_ref_const_inv stty v s t HShape) as [l HValue].
  exists l. exact HValue.
Qed.

Lemma return_deref_const_shape_progress :
  forall heap stty v s t rho k,
    TcHeap (heap, stty) ->
    TcVal
      (stty, v, Ty_Ref (Rgn_Const true true s) t) ->
    RuntimeValShape stty (Ty_Ref (Rgn_Const true true s) t) v ->
    CanStep
      (StReturn heap v (KDeRef (Rgn_Const true false s) rho k)).
Proof.
  intros heap stty v s t rho k HTcHeap HTcVal HShape.
  destruct (RuntimeValShape_ref_const_inv stty v s t HShape) as [l HValue].
  subst.
  pose proof (TcVal_loc_find_ST stty s l t HTcVal) as HFindST.
  destruct (TcHeap_find_ST_find_H heap stty (s, l) t HTcHeap HFindST)
    as [value HFindH].
  apply return_frame_ready_progress.
  simpl.
  exists l, s, value.
  repeat split; auto.
Qed.

Lemma return_concat_left_shape_progress :
  forall heap stty v e2 env rho k,
    RuntimeValShape stty Ty_Effect v ->
    CanStep (StReturn heap v (KConcatL e2 env rho k)).
Proof.
  intros heap stty v e2 env rho k HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_effect_inv; eauto.
Qed.

Lemma return_concat_right_shape_progress :
  forall heap stty v theta k,
    RuntimeValShape stty Ty_Effect v ->
    CanStep (StReturn heap v (KConcatR theta k)).
Proof.
  intros heap stty v theta k HShape.
  apply return_frame_ready_progress.
  simpl.
  now eapply RuntimeValShape_effect_inv; eauto.
Qed.

Lemma typed_eval_sequential_head_progress_unindexed :
  forall heap env rho e k stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, e, t, eff) ->
    SequentialHead e ->
    EvalHeadRegionsResolved rho e ->
    CanStep (StEval heap env rho e k).
Proof.
  intros heap env rho e k stty ctxt rgns t eff
    HTcHeap HTcRho HTcEnv HTcExp HSequential HResolved.
  destruct e; simpl in HSequential, HResolved; try contradiction.
  - exists Silent, (StReturn heap (Num n) k).
    constructor.
  - exists Silent, (StReturn heap (Bit b) k).
    constructor.
  - inversion HTcExp; subst.
    match goal with
    | HFindT : find_T v ctxt = Some ?ty |- _ =>
        destruct (TcEnv_find_E stty rho env ctxt v ty HTcEnv HFindT)
          as [value HFind]
    end.
    exists Silent, (StReturn heap value k).
    now constructor.
  - exists Silent, (StReturn heap (Cls (env, rho, Mu v v0 e1 e2)) k).
    constructor.
  - exists Silent, (StReturn heap (Cls (env, rho, Lambda v e)) k).
    constructor.
  - exists Silent, (StEval heap env rho e1 (KMuAppFun e2 env rho k)).
    constructor.
  - exists Silent, (StEval heap env rho e (KRgnApp r rho k)).
    constructor.
  - exists Silent, (StEval heap env rho e1 (KEffAppFun e2 env rho k)).
    constructor.
  - exists Silent, (StEval heap env rho e1 (KCond e2 e3 env rho k)).
    constructor.
  - exists Silent, (StEval heap env rho e (KRef r rho k)).
    constructor.
  - exists Silent, (StEval heap env rho e (KDeRef r rho k)).
    constructor.
  - exists Silent, (StEval heap env rho e1 (KAssignLoc r e2 env rho k)).
    constructor.
  - exists Silent, (StEval heap env rho e1 (KPlusL e2 env rho k)).
    constructor.
  - exists Silent, (StEval heap env rho e1 (KMinusL e2 env rho k)).
    constructor.
  - exists Silent, (StEval heap env rho e1 (KTimesL e2 env rho k)).
    constructor.
  - exists Silent, (StEval heap env rho e1 (KEqL e2 env rho k)).
    constructor.
  - destruct HResolved as [rv HFind].
    exists Silent, (StReturn heap (Eff (Some (singleton_set (CA_AllocAbs rv)))) k).
    now constructor.
  - destruct HResolved as [rv HFind].
    exists Silent, (StReturn heap (Eff (Some (singleton_set (CA_ReadAbs rv)))) k).
    now constructor.
  - destruct HResolved as [rv HFind].
    exists Silent, (StReturn heap (Eff (Some (singleton_set (CA_WriteAbs rv)))) k).
    now constructor.
  - exists Silent, (StEval heap env rho e (KReadConc k)).
    constructor.
  - exists Silent, (StEval heap env rho e (KWriteConc k)).
    constructor.
  - exists Silent, (StEval heap env rho e1 (KConcatL e2 env rho k)).
    constructor.
  - exists Silent, (StReturn heap (Eff None) k).
    constructor.
  - exists Silent, (StReturn heap (Eff (Some empty_set)) k).
    constructor.
Qed.

Lemma typed_eval_sequential_head_progress :
  forall heap env rho e k stty ctxt rgns t eff tout,
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTKontTyped stty t tout k ->
    SequentialHead e ->
    EvalHeadRegionsResolved rho e ->
    CanStep (StEval heap env rho e k).
Proof.
  intros heap env rho e k stty ctxt rgns t eff tout
    HTcHeap HTcRho HTcEnv HTcExp _ HSequential HResolved.
  eapply typed_eval_sequential_head_progress_unindexed; eauto.
Qed.

Lemma WTStateTyped_eval_sequential_head_progress :
  forall heap env rho e k tout,
    WTStateTyped (StEval heap env rho e k) tout ->
    SequentialHead e ->
    EvalHeadRegionsResolved rho e ->
    CanStep (StEval heap env rho e k).
Proof.
  intros heap env rho e k tout HWTState HSequential HResolved.
  inversion HWTState; subst.
  eapply typed_eval_sequential_head_progress; eauto.
Qed.

Inductive WTStateRuntimeShape : State -> Tau -> Prop :=
| WTSRS_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontTyped stty t tout k ->
      WTStateRuntimeShape (StEval heap env rho e k) tout
| WTSRS_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      WTKontTyped stty t tout k ->
      RuntimeValShape stty t v ->
      WTStateRuntimeShape (StReturn heap v k) tout
| WTSRS_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      WTStateRuntimeShape (StDone heap v) t.

Lemma WTStateRuntimeShape_forget :
  forall state t,
    WTStateRuntimeShape state t ->
    WTStateTyped state t.
Proof.
  intros state t HState.
  inversion HState; subst; econstructor; eauto.
Qed.

Lemma WTStateRuntimeShape_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateRuntimeShape (initial_state heap env rho e) t.
Proof.
  intros.
  unfold initial_state.
  econstructor; eauto.
  constructor.
Qed.

Lemma WTStateRuntimeShape_return_progress :
  forall heap v k tout,
    WTStateRuntimeShape (StReturn heap v k) tout ->
    CanStep (StReturn heap v k).
Proof.
  intros heap v k tout HState.
  inversion HState; subst.
  eapply typed_return_runtime_shape_progress; eauto.
Qed.

Lemma WTStateRuntimeShape_eval_sequential_head_progress :
  forall heap env rho e k tout,
    WTStateRuntimeShape (StEval heap env rho e k) tout ->
    SequentialHead e ->
    EvalHeadRegionsResolved rho e ->
    CanStep (StEval heap env rho e k).
Proof.
  intros heap env rho e k tout HState HSequential HResolved.
  inversion HState; subst.
  eapply typed_eval_sequential_head_progress; eauto.
Qed.

Lemma WTStateRuntimeShape_not_stuck :
  forall state tout,
    WTStateRuntimeShape state tout ->
    (forall heap env rho e k,
        state = StEval heap env rho e k ->
        SequentialHead e /\ EvalHeadRegionsResolved rho e) ->
    NotStuck state.
Proof.
  intros state tout HState HEvalReady.
  destruct HState.
  - right.
    destruct (HEvalReady heap env rho e k eq_refl) as [HSeq HResolved].
    eapply typed_eval_sequential_head_progress; eauto.
  - right.
    eapply typed_return_runtime_shape_progress; eauto.
  - left. constructor.
Qed.

Inductive WTStateRuntimeEnvShape : State -> Tau -> Prop :=
| WTSRES_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      RuntimeEnvShape stty rho env ctxt ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontTyped stty t tout k ->
      WTStateRuntimeEnvShape (StEval heap env rho e k) tout
| WTSRES_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      WTKontTyped stty t tout k ->
      RuntimeValShape stty t v ->
      WTStateRuntimeEnvShape (StReturn heap v k) tout
| WTSRES_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      RuntimeValShape stty t v ->
      WTStateRuntimeEnvShape (StDone heap v) t.

Lemma WTStateRuntimeEnvShape_forget :
  forall state t,
    WTStateRuntimeEnvShape state t ->
    WTStateRuntimeShape state t.
Proof.
  intros state t HState.
  inversion HState; subst; econstructor; eauto.
Qed.

Lemma WTStateRuntimeEnvShape_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    RuntimeEnvShape stty rho env ctxt ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateRuntimeEnvShape (initial_state heap env rho e) t.
Proof.
  intros.
  unfold initial_state.
  econstructor; eauto.
  constructor.
Qed.

Lemma WTStateRuntimeEnvShape_var_value :
  forall heap env rho x k tout,
    WTStateRuntimeEnvShape (StEval heap env rho (Var x) k) tout ->
    exists stty value t,
      find_E x env = Some value /\
      RuntimeValShape stty (subst_rho rho t) value.
Proof.
  intros heap env rho x k tout HState.
  inversion HState; subst.
  inversion H9; subst.
  match goal with
  | HEnvShape : RuntimeEnvShape ?stty rho env ?ctxt,
    HTcEnv : TcEnv (?stty, rho, env, ?ctxt),
    HTcExp : TcExp (?ctxt, ?rgns, Var x, ?t, Empty_Static_Action) |- _ =>
      destruct (RuntimeEnvShape_var_value stty rho env ctxt rgns x t
        HTcEnv HEnvShape HTcExp) as [value [HFindE HShape]];
      exists stty, value, t;
      split; assumption
  end.
Qed.

Lemma WTStateRuntimeEnvShape_not_stuck :
  forall state tout,
    WTStateRuntimeEnvShape state tout ->
    (forall heap env rho e k,
        state = StEval heap env rho e k ->
        SequentialHead e /\ EvalHeadRegionsResolved rho e) ->
    NotStuck state.
Proof.
  intros state tout HState HEvalReady.
  eapply WTStateRuntimeShape_not_stuck; eauto.
  eapply WTStateRuntimeEnvShape_forget; eauto.
Qed.
