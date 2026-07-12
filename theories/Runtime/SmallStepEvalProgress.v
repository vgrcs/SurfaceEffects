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

Require Import theories.Runtime.SmallStepProgressBase.
Require Import theories.Runtime.SmallStepReturnProgress.

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
