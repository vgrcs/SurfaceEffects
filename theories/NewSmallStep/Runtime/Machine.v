From Stdlib Require Import List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Ascii.

Require Import theories.NewSmallStep.Core.Effects.
Require Import theories.NewSmallStep.Core.Syntax.
Require Import theories.NewSmallStep.Core.Values.

Import ListNotations.

Fixpoint env_lookup (x : VarId) (env : NEnv) : option NVal :=
  match env with
  | EnvNil => None
  | EnvCons y v env' =>
      if ascii_dec x y then Some v else env_lookup x env'
  end.

Definition env_extend (x : VarId) (v : NVal) (env : NEnv) : NEnv :=
  EnvCons x v env.

Fixpoint heap_lookup (r : RegionId) (l : Location)
    (heap : Heap) : option NVal :=
  match heap with
  | [] => None
  | (r', l', v) :: heap' =>
      if Nat.eqb r r' && Nat.eqb l l'
      then Some v
      else heap_lookup r l heap'
  end.

Fixpoint heap_update (r : RegionId) (l : Location)
    (v : NVal) (heap : Heap) : Heap :=
  match heap with
  | [] => []
  | (r', l', old) :: heap' =>
      if Nat.eqb r r' && Nat.eqb l l'
      then (r', l', v) :: heap'
      else (r', l', old) :: heap_update r l v heap'
  end.

Definition fresh_location (heap : Heap) : Location :=
  List.length heap.

Definition heap_alloc (r : RegionId) (v : NVal)
    (heap : Heap) : Location * Heap :=
  let l := fresh_location heap in
  (l, (r, l, v) :: heap).

Inductive NKont :=
| KDone : NKont
| KMuAppFun : NExpr -> NEnv -> Rho -> NKont -> NKont
| KMuAppArg : NEnv -> Rho -> VarId -> VarId -> NExpr -> NExpr -> NKont -> NKont
| KEffAppFun : NExpr -> NEnv -> Rho -> NKont -> NKont
| KEffAppArg : NEnv -> Rho -> VarId -> VarId -> NExpr -> NExpr -> NKont -> NKont
| KRgnApp : RegionExpr -> Rho -> NKont -> NKont
| KCond : NExpr -> NExpr -> NEnv -> Rho -> NKont -> NKont
| KRef : RegionId -> NKont -> NKont
| KDeref : RegionExpr -> NKont -> NKont
| KAssignLoc : RegionExpr -> NExpr -> NEnv -> Rho -> NKont -> NKont
| KAssignVal : RegionExpr -> NVal -> NKont -> NKont
| KPlusL : NExpr -> NEnv -> Rho -> NKont -> NKont
| KPlusR : nat -> NKont -> NKont
| KMinusL : NExpr -> NEnv -> Rho -> NKont -> NKont
| KMinusR : nat -> NKont -> NKont
| KTimesL : NExpr -> NEnv -> Rho -> NKont -> NKont
| KTimesR : nat -> NKont -> NKont
| KEqL : NExpr -> NEnv -> Rho -> NKont -> NKont
| KEqR : nat -> NKont -> NKont
| KReadConc : NKont -> NKont
| KWriteConc : NKont -> NKont
| KConcatL : NExpr -> NEnv -> Rho -> NKont -> NKont
| KConcatR : Summary -> NKont -> NKont.

Inductive NState :=
| StEval : Heap -> NEnv -> Rho -> NExpr -> NKont -> NState
| StReturn : Heap -> NVal -> NKont -> NState
| StDone : Heap -> NVal -> NState.

Inductive NLabel :=
| LSilent : NLabel
| LAction : DynamicAction -> NLabel.

Definition label_trace (label : NLabel) : Trace :=
  match label with
  | LSilent => nil
  | LAction da => da :: nil
  end.

Inductive NStep : NState -> NLabel -> NState -> Prop :=
| StepConst :
    forall heap env rho n k,
      NStep
        (StEval heap env rho (EConst n) k)
        LSilent
        (StReturn heap (VNat n) k)
| StepBool :
    forall heap env rho b k,
      NStep
        (StEval heap env rho (EBool b) k)
        LSilent
        (StReturn heap (VBool b) k)
| StepVar :
    forall heap env rho x v k,
      env_lookup x env = Some v ->
      NStep
        (StEval heap env rho (EVar x) k)
        LSilent
        (StReturn heap v k)
| StepMu :
    forall heap env rho f x ec ee k,
      NStep
        (StEval heap env rho (EMu f x ec ee) k)
        LSilent
        (StReturn heap (VClosure env rho f x ec ee) k)
| StepLambdaRgn :
    forall heap env rho x e k,
      NStep
        (StEval heap env rho (ELambdaRgn x e) k)
        LSilent
        (StReturn heap (VRegionClosure env rho x e) k)
| StepMuApp :
    forall heap env rho ef ea k,
      NStep
        (StEval heap env rho (EMuApp ef ea) k)
        LSilent
        (StEval heap env rho ef (KMuAppFun ea env rho k))
| StepMuAppFun :
    forall heap env rho ea k closure_env closure_rho f x ec ee,
      NStep
        (StReturn heap
          (VClosure closure_env closure_rho f x ec ee)
          (KMuAppFun ea env rho k))
        LSilent
        (StEval heap env rho ea
          (KMuAppArg closure_env closure_rho f x ec ee k))
| StepMuAppArg :
    forall heap v_arg closure_env closure_rho f x ec ee k,
      NStep
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
      NStep
        (StEval heap env rho (EEffApp ef ea) k)
        LSilent
        (StEval heap env rho ef (KEffAppFun ea env rho k))
| StepEffAppFun :
    forall heap env rho ea k closure_env closure_rho f x ec ee,
      NStep
        (StReturn heap
          (VClosure closure_env closure_rho f x ec ee)
          (KEffAppFun ea env rho k))
        LSilent
        (StEval heap env rho ea
          (KEffAppArg closure_env closure_rho f x ec ee k))
| StepEffAppArg :
    forall heap v_arg closure_env closure_rho f x ec ee k,
      NStep
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
| StepRgnApp :
    forall heap env rho er r k,
      NStep
        (StEval heap env rho (ERgnApp er r) k)
        LSilent
        (StEval heap env rho er (KRgnApp r rho k))
| StepRgnAppReturn :
    forall heap closure_env closure_rho arg_rho x e r r_val k,
      eval_region arg_rho r = Some r_val ->
      NStep
        (StReturn heap (VRegionClosure closure_env closure_rho x e)
          (KRgnApp r arg_rho k))
        LSilent
        (StEval heap closure_env (rho_extend x r_val closure_rho) e k)
| StepEmpty :
    forall heap env rho k,
      NStep
        (StEval heap env rho EEmpty k)
        LSilent
        (StReturn heap (VSummary (SummarySet nil)) k)
| StepTop :
    forall heap env rho k,
      NStep
        (StEval heap env rho ETop k)
        LSilent
        (StReturn heap (VSummary SummaryTop) k)
| StepCond :
    forall heap env rho e et ef k,
      NStep
        (StEval heap env rho (ECond e et ef) k)
        LSilent
        (StEval heap env rho e (KCond et ef env rho k))
| StepCondTrue :
    forall heap et ef env rho k,
      NStep
        (StReturn heap (VBool true) (KCond et ef env rho k))
        LSilent
        (StEval heap env rho et k)
| StepCondFalse :
    forall heap et ef env rho k,
      NStep
        (StReturn heap (VBool false) (KCond et ef env rho k))
        LSilent
        (StEval heap env rho ef k)
| StepRef :
    forall heap env rho r e r_val k,
      eval_region rho r = Some r_val ->
      NStep
        (StEval heap env rho (ERef r e) k)
        LSilent
        (StEval heap env rho e (KRef r_val k))
| StepRefReturn :
    forall heap v r_val k l heap',
      heap_alloc r_val v heap = (l, heap') ->
      NStep
        (StReturn heap v (KRef r_val k))
        (LAction (DAlloc r_val l))
        (StReturn heap' (VLoc r_val l) k)
| StepDeref :
    forall heap env rho r e k,
      NStep
        (StEval heap env rho (EDeref r e) k)
        LSilent
        (StEval heap env rho e (KDeref r k))
| StepDerefReturn :
    forall heap r_static r l v k,
      heap_lookup r l heap = Some v ->
      NStep
        (StReturn heap (VLoc r l) (KDeref r_static k))
        (LAction (DRead r l))
        (StReturn heap v k)
| StepAssign :
    forall heap env rho r ea ev k,
      NStep
        (StEval heap env rho (EAssign r ea ev) k)
        LSilent
        (StEval heap env rho ea (KAssignLoc r ev env rho k))
| StepAssignLoc :
    forall heap r_static ev env rho r l k,
      NStep
        (StReturn heap (VLoc r l) (KAssignLoc r_static ev env rho k))
        LSilent
        (StEval heap env rho ev (KAssignVal r_static (VLoc r l) k))
| StepAssignVal :
    forall heap r_static r l v k,
      NStep
        (StReturn heap v (KAssignVal r_static (VLoc r l) k))
        (LAction (DWrite r l))
        (StReturn (heap_update r l v heap) VUnit k)
| StepPlus :
    forall heap env rho e1 e2 k,
      NStep
        (StEval heap env rho (EPlus e1 e2) k)
        LSilent
        (StEval heap env rho e1 (KPlusL e2 env rho k))
| StepPlusL :
    forall heap n e2 env rho k,
      NStep
        (StReturn heap (VNat n) (KPlusL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KPlusR n k))
| StepPlusR :
    forall heap n1 n2 k,
      NStep
        (StReturn heap (VNat n2) (KPlusR n1 k))
        LSilent
        (StReturn heap (VNat (n1 + n2)) k)
| StepMinus :
    forall heap env rho e1 e2 k,
      NStep
        (StEval heap env rho (EMinus e1 e2) k)
        LSilent
        (StEval heap env rho e1 (KMinusL e2 env rho k))
| StepMinusL :
    forall heap n e2 env rho k,
      NStep
        (StReturn heap (VNat n) (KMinusL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KMinusR n k))
| StepMinusR :
    forall heap n1 n2 k,
      NStep
        (StReturn heap (VNat n2) (KMinusR n1 k))
        LSilent
        (StReturn heap (VNat (n1 - n2)) k)
| StepTimes :
    forall heap env rho e1 e2 k,
      NStep
        (StEval heap env rho (ETimes e1 e2) k)
        LSilent
        (StEval heap env rho e1 (KTimesL e2 env rho k))
| StepTimesL :
    forall heap n e2 env rho k,
      NStep
        (StReturn heap (VNat n) (KTimesL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KTimesR n k))
| StepTimesR :
    forall heap n1 n2 k,
      NStep
        (StReturn heap (VNat n2) (KTimesR n1 k))
        LSilent
        (StReturn heap (VNat (n1 * n2)) k)
| StepEq :
    forall heap env rho e1 e2 k,
      NStep
        (StEval heap env rho (EEq e1 e2) k)
        LSilent
        (StEval heap env rho e1 (KEqL e2 env rho k))
| StepEqL :
    forall heap n e2 env rho k,
      NStep
        (StReturn heap (VNat n) (KEqL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KEqR n k))
| StepEqR :
    forall heap n1 n2 k,
      NStep
        (StReturn heap (VNat n2) (KEqR n1 k))
        LSilent
        (StReturn heap (VBool (Nat.eqb n1 n2)) k)
| StepAllocAbs :
    forall heap env rho r r_val k,
      eval_region rho r = Some r_val ->
      NStep
        (StEval heap env rho (EAllocAbs r) k)
        LSilent
        (StReturn heap (VSummary (SummarySet [CAllocAbs r_val])) k)
| StepReadAbs :
    forall heap env rho r r_val k,
      eval_region rho r = Some r_val ->
      NStep
        (StEval heap env rho (EReadAbs r) k)
        LSilent
        (StReturn heap (VSummary (SummarySet [CReadAbs r_val])) k)
| StepWriteAbs :
    forall heap env rho r r_val k,
      eval_region rho r = Some r_val ->
      NStep
        (StEval heap env rho (EWriteAbs r) k)
        LSilent
        (StReturn heap (VSummary (SummarySet [CWriteAbs r_val])) k)
| StepReadConc :
    forall heap env rho e k,
      NStep
        (StEval heap env rho (EReadConc e) k)
        LSilent
        (StEval heap env rho e (KReadConc k))
| StepReadConcReturn :
    forall heap r l k,
      NStep
        (StReturn heap (VLoc r l) (KReadConc k))
        LSilent
        (StReturn heap (VSummary (SummarySet [CReadConc r l])) k)
| StepWriteConc :
    forall heap env rho e k,
      NStep
        (StEval heap env rho (EWriteConc e) k)
        LSilent
        (StEval heap env rho e (KWriteConc k))
| StepWriteConcReturn :
    forall heap r l k,
      NStep
        (StReturn heap (VLoc r l) (KWriteConc k))
        LSilent
        (StReturn heap (VSummary (SummarySet [CWriteConc r l])) k)
| StepConcat :
    forall heap env rho e1 e2 k,
      NStep
        (StEval heap env rho (EConcat e1 e2) k)
        LSilent
        (StEval heap env rho e1 (KConcatL e2 env rho k))
| StepConcatL :
    forall heap theta1 e2 env rho k,
      NStep
        (StReturn heap (VSummary theta1) (KConcatL e2 env rho k))
        LSilent
        (StEval heap env rho e2 (KConcatR theta1 k))
| StepConcatR :
    forall heap theta1 theta2 k,
      NStep
        (StReturn heap (VSummary theta2) (KConcatR theta1 k))
        LSilent
        (StReturn heap (VSummary (summary_union theta1 theta2)) k)
| StepReturnDone :
    forall heap v,
      NStep
        (StReturn heap v KDone)
        LSilent
        (StDone heap v).

Inductive NTerminal : NState -> Prop :=
| TerminalDone :
    forall heap v,
      NTerminal (StDone heap v).

Definition NInitialState (heap : Heap) (env : NEnv) (rho : Rho)
    (e : NExpr) : NState :=
  StEval heap env rho e KDone.
