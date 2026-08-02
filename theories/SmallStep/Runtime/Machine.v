From Stdlib Require Import List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Ascii.

Require Import theories.SmallStep.Core.Effects.
Require Import theories.SmallStep.Core.Syntax.
Require Import theories.SmallStep.Core.Values.

Import ListNotations.

Fixpoint env_lookup (x : VarId) (env : Env) : option Val :=
  match env with
  | EnvNil => None
  | EnvCons y v env' =>
      if ascii_dec x y then Some v else env_lookup x env'
  end.

Definition env_extend (x : VarId) (v : Val) (env : Env) : Env :=
  EnvCons x v env.

Fixpoint heap_lookup (r : RegionId) (l : Location)
    (heap : Heap) : option Val :=
  match heap with
  | [] => None
  | (r', l', v) :: heap' =>
      if Nat.eqb r r' && Nat.eqb l l'
      then Some v
      else heap_lookup r l heap'
  end.

Fixpoint heap_update (r : RegionId) (l : Location)
    (v : Val) (heap : Heap) : Heap :=
  match heap with
  | [] => []
  | (r', l', old) :: heap' =>
      if Nat.eqb r r' && Nat.eqb l l'
      then (r', l', v) :: heap'
      else (r', l', old) :: heap_update r l v heap'
  end.

Definition fresh_location (heap : Heap) : Location :=
  List.length heap.

Definition heap_alloc (r : RegionId) (v : Val)
    (heap : Heap) : Location * Heap :=
  let l := fresh_location heap in
  (l, (r, l, v) :: heap).

Inductive Kont :=
| KDone : Kont
| KMuAppFun : Expr -> Env -> Rho -> Kont -> Kont
| KMuAppArg : Env -> Rho -> VarId -> VarId -> Expr -> Expr -> Kont -> Kont
| KEffAppFun : Expr -> Env -> Rho -> Kont -> Kont
| KEffAppArg : Env -> Rho -> VarId -> VarId -> Expr -> Expr -> Kont -> Kont
| KPairParEff1 : Expr -> Expr -> Expr -> Expr -> Env -> Rho -> Kont -> Kont
| KPairParEff2 : Expr -> Expr -> Expr -> Expr -> Env -> Rho -> Summary -> Kont -> Kont
| KPairParFallbackLeft : Expr -> Expr -> Env -> Rho -> Kont -> Kont
| KPairParFallbackRight : Val -> Kont -> Kont
| KRgnApp : RegionExpr -> Rho -> Kont -> Kont
| KCond : Expr -> Expr -> Env -> Rho -> Kont -> Kont
| KRef : RegionId -> Kont -> Kont
| KDeref : RegionExpr -> Kont -> Kont
| KAssignLoc : RegionExpr -> Expr -> Env -> Rho -> Kont -> Kont
| KAssignVal : RegionExpr -> Val -> Kont -> Kont
| KPlusL : Expr -> Env -> Rho -> Kont -> Kont
| KPlusR : nat -> Kont -> Kont
| KMinusL : Expr -> Env -> Rho -> Kont -> Kont
| KMinusR : nat -> Kont -> Kont
| KTimesL : Expr -> Env -> Rho -> Kont -> Kont
| KTimesR : nat -> Kont -> Kont
| KEqL : Expr -> Env -> Rho -> Kont -> Kont
| KEqR : nat -> Kont -> Kont
| KReadConc : Kont -> Kont
| KWriteConc : Kont -> Kont
| KConcatL : Expr -> Env -> Rho -> Kont -> Kont
| KConcatR : Summary -> Kont -> Kont.

Inductive State :=
| StEval : Heap -> Env -> Rho -> Expr -> Kont -> State
| StReturn : Heap -> Val -> Kont -> State
| StDone : Heap -> Val -> State
| StPairParRun : State -> State -> Trace -> Trace -> Kont -> State
| StError : Heap -> State.

Fixpoint state_heap (state : State) : Heap :=
  match state with
  | StEval heap _ _ _ _ => heap
  | StReturn heap _ _ => heap
  | StDone heap _ => heap
  | StPairParRun left_state _ _ _ _ => state_heap left_state
  | StError heap => heap
  end.

Fixpoint with_state_heap (heap : Heap) (state : State) : State :=
  match state with
  | StEval _ env rho e k => StEval heap env rho e k
  | StReturn _ v k => StReturn heap v k
  | StDone _ v => StDone heap v
  | StPairParRun left_state right_state phi_left phi_right k =>
      StPairParRun
        (with_state_heap heap left_state)
        (with_state_heap heap right_state)
        phi_left
        phi_right
        k
  | StError _ => StError heap
  end.

Inductive Label :=
| LSilent : Label
| LAction : DynamicAction -> Label.

Definition label_trace (label : Label) : Trace :=
  match label with
  | LSilent => nil
  | LAction da => da :: nil
  end.

Inductive Step : State -> Label -> State -> Prop :=
| StepConst :
    forall heap env rho n k,
      Step
        (StEval heap env rho (EConst n) k)
        LSilent
        (StReturn heap (VNat n) k)
| StepBool :
    forall heap env rho b k,
      Step
        (StEval heap env rho (EBool b) k)
        LSilent
        (StReturn heap (VBool b) k)
| StepVar :
    forall heap env rho x v k,
      env_lookup x env = Some v ->
      Step
        (StEval heap env rho (EVar x) k)
        LSilent
        (StReturn heap v k)
| StepMu :
    forall heap env rho f x ec ee k,
      Step
        (StEval heap env rho (EMu f x ec ee) k)
        LSilent
        (StReturn heap (VClosure env rho f x ec ee) k)
| StepLambdaRgn :
    forall heap env rho x e k,
      Step
        (StEval heap env rho (ELambdaRgn x e) k)
        LSilent
        (StReturn heap (VRegionClosure env rho x e) k)
| StepMuApp :
    forall heap env rho ef ea k,
      Step
        (StEval heap env rho (EMuApp ef ea) k)
        LSilent
        (StEval heap env rho ef (KMuAppFun ea env rho k))
| StepMuAppFun :
    forall heap env rho ea k closure_env closure_rho f x ec ee,
      Step
        (StReturn heap
          (VClosure closure_env closure_rho f x ec ee)
          (KMuAppFun ea env rho k))
        LSilent
        (StEval heap env rho ea
          (KMuAppArg closure_env closure_rho f x ec ee k))
| StepMuAppArg :
    forall heap v_arg closure_env closure_rho f x ec ee k,
      Step
        (StReturn heap v_arg
          (KMuAppArg closure_env closure_rho f x ec ee k))
        LSilent
        (StEval heap
          (env_extend x v_arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho
          ec
          k)
| StepEffApp :
    forall heap env rho ef ea k,
      Step
        (StEval heap env rho (EEffApp ef ea) k)
        LSilent
        (StEval heap env rho ef (KEffAppFun ea env rho k))
| StepEffAppFun :
    forall heap env rho ea k closure_env closure_rho f x ec ee,
      Step
        (StReturn heap
          (VClosure closure_env closure_rho f x ec ee)
          (KEffAppFun ea env rho k))
        LSilent
        (StEval heap env rho ea
          (KEffAppArg closure_env closure_rho f x ec ee k))
| StepEffAppArg :
    forall heap v_arg closure_env closure_rho f x ec ee k,
      Step
        (StReturn heap v_arg
          (KEffAppArg closure_env closure_rho f x ec ee k))
        LSilent
        (StEval heap
          (env_extend x v_arg
            (env_extend f
              (VClosure closure_env closure_rho f x ec ee)
              closure_env))
          closure_rho
          ee
          k)
| StepPairPar :
    forall heap env rho ef1 ea1 ef2 ea2 k,
      Step
        (StEval heap env rho
          (EPairPar (EMuApp ef1 ea1) (EMuApp ef2 ea2)) k)
        LSilent
        (StEval heap env rho (EEffApp ef1 ea1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
| StepPairParEff1 :
    forall heap theta1 ef1 ea1 ef2 ea2 env rho k,
      Step
        (StReturn heap (VSummary theta1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
        LSilent
        (StEval heap env rho (EEffApp ef2 ea2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
| StepPairParCheckPass :
    forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k,
      summary_disjointb theta1 theta2 = true ->
      Step
        (StReturn heap (VSummary theta2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
        LSilent
        (StPairParRun
          (StEval heap env rho (EMuApp ef1 ea1) KDone)
          (StEval heap env rho (EMuApp ef2 ea2) KDone)
          []
          []
          k)
| StepPairParCheckFail :
    forall heap theta1 theta2 ef1 ea1 ef2 ea2 env rho k,
      summary_disjointb theta1 theta2 = false ->
      Step
        (StReturn heap (VSummary theta2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
        LSilent
        (StEval heap env rho (EMuApp ef1 ea1)
          (KPairParFallbackLeft ef2 ea2 env rho k))
| StepPairParFallbackLeftReturn :
    forall heap v_left ef2 ea2 env rho k,
      Step
        (StReturn heap v_left
          (KPairParFallbackLeft ef2 ea2 env rho k))
        LSilent
        (StEval heap env rho (EMuApp ef2 ea2)
          (KPairParFallbackRight v_left k))
| StepPairParFallbackRightReturn :
    forall heap v_left v_right k,
      Step
        (StReturn heap v_right
          (KPairParFallbackRight v_left k))
        LSilent
        (StReturn heap (VPair v_left v_right) k)
| StepPairParRunLeft :
    forall left_state right_state phi_left phi_right k label left_state',
      Step left_state label left_state' ->
      Step
        (StPairParRun left_state right_state phi_left phi_right k)
        label
        (StPairParRun
          left_state'
          (with_state_heap (state_heap left_state') right_state)
          (phi_left ++ label_trace label)
          phi_right
          k)
| StepPairParRunRight :
    forall heap v1 right_state phi_left phi_right k label right_state',
      Step right_state label right_state' ->
      Step
        (StPairParRun (StDone heap v1) right_state phi_left phi_right k)
        label
        (StPairParRun
          (with_state_heap (state_heap right_state') (StDone heap v1))
          right_state'
          phi_left
          (phi_right ++ label_trace label)
          k)
| StepPairParRunLeftError :
    forall heap right_state phi_left phi_right k,
      Step
        (StPairParRun (StError heap) right_state phi_left phi_right k)
        LSilent
        (StError heap)
| StepPairParRunRightError :
    forall heap_left v1 heap_right phi_left phi_right k,
      Step
        (StPairParRun
          (StDone heap_left v1)
          (StError heap_right)
          phi_left
          phi_right
          k)
        LSilent
        (StError heap_right)
| StepPairParRunDonePass :
    forall heap v1 v2 phi_left phi_right k,
      trace_disjointb phi_left phi_right = true ->
      Step
        (StPairParRun
          (StDone heap v1)
          (StDone heap v2)
          phi_left
          phi_right
          k)
        LSilent
        (StReturn heap (VPair v1 v2) k)
| StepPairParRunDoneFail :
    forall heap v1 v2 phi_left phi_right k,
      trace_disjointb phi_left phi_right = false ->
      Step
        (StPairParRun
          (StDone heap v1)
          (StDone heap v2)
          phi_left
          phi_right
          k)
        LSilent
        (StError heap)
| StepRgnApp :
    forall heap env rho er r k,
      Step
        (StEval heap env rho (ERgnApp er r) k)
        LSilent
        (StEval heap env rho er (KRgnApp r rho k))
| StepRgnAppReturn :
    forall heap closure_env closure_rho arg_rho x e r r_val k,
      eval_region arg_rho r = Some r_val ->
      Step
        (StReturn heap (VRegionClosure closure_env closure_rho x e)
          (KRgnApp r arg_rho k))
        LSilent
        (StEval heap closure_env (rho_extend x r_val closure_rho) e k)
| StepEmpty :
    forall heap env rho k,
      Step
        (StEval heap env rho EEmpty k)
        LSilent
        (StReturn heap (VSummary (SummarySet nil)) k)
| StepTop :
    forall heap env rho k,
      Step
        (StEval heap env rho ETop k)
        LSilent
        (StReturn heap (VSummary SummaryTop) k)
| StepCond :
    forall heap env rho e et ef k,
      Step
        (StEval heap env rho (ECond e et ef) k)
        LSilent
        (StEval heap env rho e (KCond et ef env rho k))
| StepCondTrue :
    forall heap et ef env rho k,
      Step
        (StReturn heap (VBool true) (KCond et ef env rho k))
        LSilent
        (StEval heap env rho et k)
| StepCondFalse :
    forall heap et ef env rho k,
      Step
        (StReturn heap (VBool false) (KCond et ef env rho k))
        LSilent
        (StEval heap env rho ef k)
| StepRef :
    forall heap env rho r e r_val k,
      eval_region rho r = Some r_val ->
      Step
        (StEval heap env rho (ERef r e) k)
        LSilent
        (StEval heap env rho e (KRef r_val k))
| StepRefReturn :
    forall heap v r_val k l heap',
      heap_alloc r_val v heap = (l, heap') ->
      Step
        (StReturn heap v (KRef r_val k))
        (LAction (DAlloc r_val l))
        (StReturn heap' (VLoc r_val l) k)
| StepDeref :
    forall heap env rho r e k,
      Step
        (StEval heap env rho (EDeref r e) k)
        LSilent
        (StEval heap env rho e (KDeref r k))
| StepDerefReturn :
    forall heap r_static r l v k,
      heap_lookup r l heap = Some v ->
      Step
        (StReturn heap (VLoc r l) (KDeref r_static k))
        (LAction (DRead r l))
        (StReturn heap v k)
| StepAssign :
    forall heap env rho r ea ev k,
      Step
        (StEval heap env rho (EAssign r ea ev) k)
        LSilent
        (StEval heap env rho ea (KAssignLoc r ev env rho k))
| StepAssignLoc :
    forall heap r_static ev env rho r l k,
      Step
        (StReturn heap (VLoc r l) (KAssignLoc r_static ev env rho k))
        LSilent
        (StEval heap env rho ev (KAssignVal r_static (VLoc r l) k))
| StepAssignVal :
    forall heap r_static r l v k,
      Step
        (StReturn heap v (KAssignVal r_static (VLoc r l) k))
        (LAction (DWrite r l))
        (StReturn (heap_update r l v heap) VUnit k)
| StepPlus :
    forall heap env rho e1 e2 k,
      Step
        (StEval heap env rho (EPlus e1 e2) k)
        LSilent
        (StEval heap env rho e1 (KPlusL e2 env rho k))
| StepPlusL :
    forall heap n e2 env rho k,
      Step
        (StReturn heap (VNat n) (KPlusL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KPlusR n k))
| StepPlusR :
    forall heap n1 n2 k,
      Step
        (StReturn heap (VNat n2) (KPlusR n1 k))
        LSilent
        (StReturn heap (VNat (n1 + n2)) k)
| StepMinus :
    forall heap env rho e1 e2 k,
      Step
        (StEval heap env rho (EMinus e1 e2) k)
        LSilent
        (StEval heap env rho e1 (KMinusL e2 env rho k))
| StepMinusL :
    forall heap n e2 env rho k,
      Step
        (StReturn heap (VNat n) (KMinusL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KMinusR n k))
| StepMinusR :
    forall heap n1 n2 k,
      Step
        (StReturn heap (VNat n2) (KMinusR n1 k))
        LSilent
        (StReturn heap (VNat (n1 - n2)) k)
| StepTimes :
    forall heap env rho e1 e2 k,
      Step
        (StEval heap env rho (ETimes e1 e2) k)
        LSilent
        (StEval heap env rho e1 (KTimesL e2 env rho k))
| StepTimesL :
    forall heap n e2 env rho k,
      Step
        (StReturn heap (VNat n) (KTimesL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KTimesR n k))
| StepTimesR :
    forall heap n1 n2 k,
      Step
        (StReturn heap (VNat n2) (KTimesR n1 k))
        LSilent
        (StReturn heap (VNat (n1 * n2)) k)
| StepEq :
    forall heap env rho e1 e2 k,
      Step
        (StEval heap env rho (EEq e1 e2) k)
        LSilent
        (StEval heap env rho e1 (KEqL e2 env rho k))
| StepEqL :
    forall heap n e2 env rho k,
      Step
        (StReturn heap (VNat n) (KEqL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KEqR n k))
| StepEqR :
    forall heap n1 n2 k,
      Step
        (StReturn heap (VNat n2) (KEqR n1 k))
        LSilent
        (StReturn heap (VBool (Nat.eqb n1 n2)) k)
| StepAllocAbs :
    forall heap env rho r r_val k,
      eval_region rho r = Some r_val ->
      Step
        (StEval heap env rho (EAllocAbs r) k)
        LSilent
        (StReturn heap (VSummary (SummarySet [CAllocAbs r_val])) k)
| StepReadAbs :
    forall heap env rho r r_val k,
      eval_region rho r = Some r_val ->
      Step
        (StEval heap env rho (EReadAbs r) k)
        LSilent
        (StReturn heap (VSummary (SummarySet [CReadAbs r_val])) k)
| StepWriteAbs :
    forall heap env rho r r_val k,
      eval_region rho r = Some r_val ->
      Step
        (StEval heap env rho (EWriteAbs r) k)
        LSilent
        (StReturn heap (VSummary (SummarySet [CWriteAbs r_val])) k)
| StepReadConc :
    forall heap env rho e k,
      Step
        (StEval heap env rho (EReadConc e) k)
        LSilent
        (StEval heap env rho e (KReadConc k))
| StepReadConcReturn :
    forall heap r l k,
      Step
        (StReturn heap (VLoc r l) (KReadConc k))
        LSilent
        (StReturn heap (VSummary (SummarySet [CReadConc r l])) k)
| StepWriteConc :
    forall heap env rho e k,
      Step
        (StEval heap env rho (EWriteConc e) k)
        LSilent
        (StEval heap env rho e (KWriteConc k))
| StepWriteConcReturn :
    forall heap r l k,
      Step
        (StReturn heap (VLoc r l) (KWriteConc k))
        LSilent
        (StReturn heap (VSummary (SummarySet [CWriteConc r l])) k)
| StepConcat :
    forall heap env rho e1 e2 k,
      Step
        (StEval heap env rho (EConcat e1 e2) k)
        LSilent
        (StEval heap env rho e1 (KConcatL e2 env rho k))
| StepConcatL :
    forall heap theta1 e2 env rho k,
      Step
        (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KConcatR theta1 k))
| StepConcatR :
    forall heap theta1 theta2 k,
      Step
        (StReturn heap (VSummary theta2) (KConcatR theta1 k))
        LSilent
        (StReturn heap (VSummary (summary_union theta1 theta2)) k)
| StepReturnDone :
    forall heap v,
      Step
        (StReturn heap v KDone)
        LSilent
        (StDone heap v).

Inductive Terminal : State -> Prop :=
| TerminalDone :
    forall heap v,
      Terminal (StDone heap v)
| TerminalError :
    forall heap,
      Terminal (StError heap).

Definition InitialState (heap : Heap) (env : Env) (rho : Rho)
    (e : Expr) : State :=
  StEval heap env rho e KDone.
