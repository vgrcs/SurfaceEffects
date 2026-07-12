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
