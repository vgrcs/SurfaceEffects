Require Import theories.Runtime.HeapTyping.
Require Import theories.Runtime.SmallStep.
Require Import theories.Core.Regions.
Require Import theories.Typing.TypeSyntax.
Require Import theories.Typing.TypingJudgments.

Inductive WTKont : Sigma -> Kont -> Prop :=
| WTK_Done :
    forall stty,
      WTKont stty KDone
| WTK_MuAppFun :
    forall stty ea env rho k ctxt rgns tya effa,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, ea, tya, effa) ->
      WTKont stty k ->
      WTKont stty (KMuAppFun ea env rho k)
| WTK_MuAppArg :
    forall stty env rho f x ec ee k ctxt rgns tya effc tyc effe,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya) ctxt,
          rgns, ec, tyc, effc) ->
      WTKont stty k ->
      WTKont stty (KMuAppArg env rho f x ec ee k)
| WTK_RgnApp :
    forall stty w rho k rgns,
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKont stty k ->
      WTKont stty (KRgnApp w rho k)
| WTK_EffAppFun :
    forall stty ea env rho k ctxt rgns tya effa,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, ea, tya, effa) ->
      WTKont stty k ->
      WTKont stty (KEffAppFun ea env rho k)
| WTK_EffAppArg :
    forall stty env rho f x ec ee k ctxt rgns tya effc tyc effe,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya) ctxt,
          rgns, ee, Ty_Effect, effe) ->
      WTKont stty k ->
      WTKont stty (KEffAppArg env rho f x ec ee k)
| WTK_Cond :
    forall stty et ef env rho k ctxt rgns t efft efff,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, et, t, efft) ->
      TcExp (ctxt, rgns, ef, t, efff) ->
      WTKont stty k ->
      WTKont stty (KCond et ef env rho k)
| WTK_Ref :
    forall stty w rho k rgns,
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKont stty k ->
      WTKont stty (KRef w rho k)
| WTK_DeRef :
    forall stty w rho k rgns,
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKont stty k ->
      WTKont stty (KDeRef w rho k)
| WTK_AssignLoc :
    forall stty w ev env rho k ctxt rgns t veff,
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, ev, t, veff) ->
      WTKont stty k ->
      WTKont stty (KAssignLoc w ev env rho k)
| WTK_AssignVal :
    forall stty w l rho k rgns,
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKont stty k ->
      WTKont stty (KAssignVal w l rho k)
| WTK_PlusL :
    forall stty e2 env rho k ctxt rgns eff2,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKont stty k ->
      WTKont stty (KPlusL e2 env rho k)
| WTK_PlusR :
    forall stty n k,
      WTKont stty k ->
      WTKont stty (KPlusR n k)
| WTK_MinusL :
    forall stty e2 env rho k ctxt rgns eff2,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKont stty k ->
      WTKont stty (KMinusL e2 env rho k)
| WTK_MinusR :
    forall stty n k,
      WTKont stty k ->
      WTKont stty (KMinusR n k)
| WTK_TimesL :
    forall stty e2 env rho k ctxt rgns eff2,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKont stty k ->
      WTKont stty (KTimesL e2 env rho k)
| WTK_TimesR :
    forall stty n k,
      WTKont stty k ->
      WTKont stty (KTimesR n k)
| WTK_EqL :
    forall stty e2 env rho k ctxt rgns eff2,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKont stty k ->
      WTKont stty (KEqL e2 env rho k)
| WTK_EqR :
    forall stty n k,
      WTKont stty k ->
      WTKont stty (KEqR n k)
| WTK_ReadConc :
    forall stty k,
      WTKont stty k ->
      WTKont stty (KReadConc k)
| WTK_WriteConc :
    forall stty k,
      WTKont stty k ->
      WTKont stty (KWriteConc k)
| WTK_ConcatL :
    forall stty e2 env rho k ctxt rgns eff2,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e2, Ty_Effect, eff2) ->
      WTKont stty k ->
      WTKont stty (KConcatL e2 env rho k)
| WTK_ConcatR :
    forall stty theta k,
      WTKont stty k ->
      WTKont stty (KConcatR theta k).

Inductive WTState : State -> Prop :=
| WTS_Eval :
    forall heap env rho e k stty ctxt rgns t eff,
      TcHeap (heap, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKont stty k ->
      WTState (StEval heap env rho e k)
| WTS_Return :
    forall heap v k stty t,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      WTKont stty k ->
      WTState (StReturn heap v k)
| WTS_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      WTState (StDone heap v).

Inductive WTKontTyped : Sigma -> Tau -> Tau -> Kont -> Prop :=
| WTKT_Done :
    forall stty t,
      WTKontTyped stty t t KDone
| WTKT_MuAppFun :
    forall stty ea env rho k ctxt rgns tya effa effc tyc effe tout,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, ea, tya, effa) ->
      WTKontTyped stty tyc tout k ->
      WTKontTyped stty
        (Ty_Arrow tya effc tyc effe Ty_Effect)
        tout
        (KMuAppFun ea env rho k)
| WTKT_MuAppArg :
    forall stty env rho f x ec ee k ctxt rgns tya effc tyc effe tout,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya) ctxt,
          rgns, ec, tyc, effc) ->
      WTKontTyped stty tyc tout k ->
      WTKontTyped stty tya tout (KMuAppArg env rho f x ec ee k)
| WTKT_RgnApp :
    forall stty w rho k rgns effr tyr tout,
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKontTyped stty (open (mk_rgn_type w) tyr) tout k ->
      WTKontTyped stty (Ty_ForallRgn effr tyr) tout (KRgnApp w rho k)
| WTKT_EffAppFun :
    forall stty ea env rho k ctxt rgns tya effa effc tyc effe tout,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, ea, tya, effa) ->
      WTKontTyped stty Ty_Effect tout k ->
      WTKontTyped stty
        (Ty_Arrow tya effc tyc effe Ty_Effect)
        tout
        (KEffAppFun ea env rho k)
| WTKT_EffAppArg :
    forall stty env rho f x ec ee k ctxt rgns tya effc tyc effe tout,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp
        (update_rec_T (f, Ty_Arrow tya effc tyc effe Ty_Effect) (x, tya) ctxt,
          rgns, ee, Ty_Effect, effe) ->
      WTKontTyped stty Ty_Effect tout k ->
      WTKontTyped stty tya tout (KEffAppArg env rho f x ec ee k)
| WTKT_Cond :
    forall stty et ef env rho k ctxt rgns t efft efff tout,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, et, t, efft) ->
      TcExp (ctxt, rgns, ef, t, efff) ->
      WTKontTyped stty t tout k ->
      WTKontTyped stty Ty_Boolean tout (KCond et ef env rho k)
| WTKT_Ref :
    forall stty w rho k rgns t tout s,
      w = Rgn_Const true false s ->
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKontTyped stty (Ty_Ref (mk_rgn_type w) t) tout k ->
      WTKontTyped stty t tout (KRef w rho k)
| WTKT_DeRef :
    forall stty w rho k rgns t tout s,
      w = Rgn_Const true false s ->
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      WTKontTyped stty t tout k ->
      WTKontTyped stty (Ty_Ref (mk_rgn_type w) t) tout (KDeRef w rho k)
| WTKT_AssignLoc :
    forall stty w ev env rho k ctxt rgns t veff tout s,
      w = Rgn_Const true false s ->
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, ev, t, veff) ->
      WTKontTyped stty Ty_Unit tout k ->
      WTKontTyped stty (Ty_Ref (mk_rgn_type w) t) tout
        (KAssignLoc w ev env rho k)
| WTKT_AssignVal :
    forall stty w l rho k rgns r t tout,
      TcRho (rho, rgns) ->
      TcRgn (rgns, w) ->
      find_R w rho = Some r ->
      find_ST (r, l) stty = Some t ->
      WTKontTyped stty Ty_Unit tout k ->
      WTKontTyped stty t tout (KAssignVal w l rho k)
| WTKT_PlusL :
    forall stty e2 env rho k ctxt rgns eff2 tout,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontTyped stty Ty_Natural tout k ->
      WTKontTyped stty Ty_Natural tout (KPlusL e2 env rho k)
| WTKT_PlusR :
    forall stty n k tout,
      WTKontTyped stty Ty_Natural tout k ->
      WTKontTyped stty Ty_Natural tout (KPlusR n k)
| WTKT_MinusL :
    forall stty e2 env rho k ctxt rgns eff2 tout,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontTyped stty Ty_Natural tout k ->
      WTKontTyped stty Ty_Natural tout (KMinusL e2 env rho k)
| WTKT_MinusR :
    forall stty n k tout,
      WTKontTyped stty Ty_Natural tout k ->
      WTKontTyped stty Ty_Natural tout (KMinusR n k)
| WTKT_TimesL :
    forall stty e2 env rho k ctxt rgns eff2 tout,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontTyped stty Ty_Natural tout k ->
      WTKontTyped stty Ty_Natural tout (KTimesL e2 env rho k)
| WTKT_TimesR :
    forall stty n k tout,
      WTKontTyped stty Ty_Natural tout k ->
      WTKontTyped stty Ty_Natural tout (KTimesR n k)
| WTKT_EqL :
    forall stty e2 env rho k ctxt rgns eff2 tout,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e2, Ty_Natural, eff2) ->
      WTKontTyped stty Ty_Boolean tout k ->
      WTKontTyped stty Ty_Natural tout (KEqL e2 env rho k)
| WTKT_EqR :
    forall stty n k tout,
      WTKontTyped stty Ty_Boolean tout k ->
      WTKontTyped stty Ty_Natural tout (KEqR n k)
| WTKT_ReadConc :
    forall stty k r t tout,
      WTKontTyped stty Ty_Effect tout k ->
      WTKontTyped stty (Ty_Ref (Rgn_Const true true r) t) tout
        (KReadConc k)
| WTKT_WriteConc :
    forall stty k r t tout,
      WTKontTyped stty Ty_Effect tout k ->
      WTKontTyped stty (Ty_Ref (Rgn_Const true true r) t) tout
        (KWriteConc k)
| WTKT_ConcatL :
    forall stty e2 env rho k ctxt rgns eff2 tout,
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e2, Ty_Effect, eff2) ->
      WTKontTyped stty Ty_Effect tout k ->
      WTKontTyped stty Ty_Effect tout (KConcatL e2 env rho k)
| WTKT_ConcatR :
    forall stty theta k tout,
      WTKontTyped stty Ty_Effect tout k ->
      WTKontTyped stty Ty_Effect tout (KConcatR theta k).

Inductive WTStateTyped : State -> Tau -> Prop :=
| WTST_Eval :
    forall heap env rho e k stty ctxt rgns t eff tout,
      TcHeap (heap, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) ->
      TcExp (ctxt, rgns, e, t, eff) ->
      WTKontTyped stty t tout k ->
      WTStateTyped (StEval heap env rho e k) tout
| WTST_Return :
    forall heap v k stty t tout,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      WTKontTyped stty t tout k ->
      WTStateTyped (StReturn heap v k) tout
| WTST_Done :
    forall heap v stty t,
      TcHeap (heap, stty) ->
      TcVal (stty, v, t) ->
      WTStateTyped (StDone heap v) t.

Lemma WTKont_done :
  forall stty,
    WTKont stty KDone.
Proof.
  constructor.
Qed.

Lemma WTKontTyped_forget :
  forall stty tin tout k,
    WTKontTyped stty tin tout k ->
    WTKont stty k.
Proof.
  intros stty tin tout k HWTKont.
  induction HWTKont; econstructor; eauto.
Qed.

Lemma WTStateTyped_forget :
  forall state t,
    WTStateTyped state t ->
    WTState state.
Proof.
  intros state t HWTState.
  inversion HWTState; subst; econstructor; eauto using WTKontTyped_forget.
Qed.

Lemma WTState_initial :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTState (initial_state heap env rho e).
Proof.
  intros.
  unfold initial_state.
  econstructor; eauto using WTKont_done.
Qed.

Lemma WTState_initial_typed :
  forall heap env rho e stty ctxt rgns t eff,
    TcHeap (heap, stty) ->
    TcRho (rho, rgns) ->
    TcEnv (stty, rho, env, ctxt) ->
    TcExp (ctxt, rgns, e, t, eff) ->
    WTStateTyped (initial_state heap env rho e) t.
Proof.
  intros.
  unfold initial_state.
  econstructor; eauto.
  constructor.
Qed.

Lemma WTState_done :
  forall heap v stty t,
    TcHeap (heap, stty) ->
    TcVal (stty, v, t) ->
    WTState (StDone heap v).
Proof.
  intros.
  econstructor; eauto.
Qed.

Lemma WTState_done_typed :
  forall heap v stty t,
    TcHeap (heap, stty) ->
    TcVal (stty, v, t) ->
    WTStateTyped (StDone heap v) t.
Proof.
  intros.
  econstructor; eauto.
Qed.
