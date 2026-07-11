From Stdlib Require Import List.

Require Import theories.Runtime.Heap.
Require Import theories.Core.Regions.
Require Import theories.Core.Expressions.
Require Import theories.Core.Values.
Require Import theories.Core.ComputedActions.
Require Import theories.Core.DynamicActions.

Inductive Label : Type :=
| Silent : Label
| Act : DynamicAction -> Label.

Definition label_trace (lbl : Label) : Trace :=
  match lbl with
  | Silent => nil
  | Act da => da :: nil
  end.

Inductive Kont : Type :=
| KDone : Kont
| KMuAppFun : Expr -> Env -> Rho -> Kont -> Kont
| KMuAppArg : Env -> Rho -> VarId -> VarId -> Expr -> Expr -> Kont -> Kont
| KRgnApp : Region_in_Expr -> Rho -> Kont -> Kont
| KEffAppFun : Expr -> Env -> Rho -> Kont -> Kont
| KEffAppArg : Env -> Rho -> VarId -> VarId -> Expr -> Expr -> Kont -> Kont
| KPairParEff1 : Expr -> Expr -> Expr -> Expr -> Env -> Rho -> Kont -> Kont
| KPairParEff2 : Expr -> Expr -> Expr -> Expr -> Env -> Rho -> Theta -> Kont -> Kont
| KPairParMu1 : Expr -> Expr -> Env -> Rho -> Kont -> Kont
| KPairParMu2 : Val -> Kont -> Kont
| KCond : Expr -> Expr -> Env -> Rho -> Kont -> Kont
| KRef : Region_in_Expr -> Rho -> Kont -> Kont
| KDeRef : Region_in_Expr -> Rho -> Kont -> Kont
| KAssignLoc : Region_in_Expr -> Expr -> Env -> Rho -> Kont -> Kont
| KAssignVal : Region_in_Expr -> nat -> Rho -> Kont -> Kont
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
| KConcatR : Theta -> Kont -> Kont.

Inductive State : Type :=
| StEval : Heap -> Env -> Rho -> Expr -> Kont -> State
| StReturn : Heap -> Val -> Kont -> State
| StDone : Heap -> Val -> State.

Definition initial_state (heap : Heap) (env : Env) (rho : Rho) (e : Expr) : State :=
  StEval heap env rho e KDone.

Inductive Terminal : State -> Prop :=
| Terminal_Done : forall heap v, Terminal (StDone heap v).

Inductive Step : State -> Label -> State -> Prop :=
| Step_Const :
    forall heap env rho k n,
      Step (StEval heap env rho (Const n) k) Silent (StReturn heap (Num n) k)
| Step_Bool :
    forall heap env rho k b,
      Step (StEval heap env rho (Bool b) k) Silent (StReturn heap (Bit b) k)
| Step_Var :
    forall heap env rho k x v,
      find_E x env = Some v ->
      Step (StEval heap env rho (Var x) k) Silent (StReturn heap v k)
| Step_Mu :
    forall heap env rho k f x ec ee,
      Step (StEval heap env rho (Mu f x ec ee) k) Silent
        (StReturn heap (Cls (env, rho, Mu f x ec ee)) k)
| Step_Lambda :
    forall heap env rho k x eb,
      Step (StEval heap env rho (Lambda x eb) k) Silent
        (StReturn heap (Cls (env, rho, Lambda x eb)) k)
| Step_MuApp_EvalFun :
    forall heap env rho k ef ea,
      Step (StEval heap env rho (Mu_App ef ea) k) Silent
        (StEval heap env rho ef (KMuAppFun ea env rho k))
| Step_MuApp_EvalArg :
    forall heap env rho k ea env' rho' f x ec ee,
      Step (StReturn heap (Cls (env', rho', Mu f x ec ee)) (KMuAppFun ea env rho k)) Silent
        (StEval heap env rho ea (KMuAppArg env' rho' f x ec ee k))
| Step_MuApp_EvalBody :
    forall heap v env' rho' f x ec ee k,
      Step (StReturn heap v (KMuAppArg env' rho' f x ec ee k)) Silent
        (StEval heap
          (update_rec_E (f, Cls (env', rho', Mu f x ec ee)) (x, v) env')
          rho' ec k)
| Step_RgnApp_EvalFun :
    forall heap env rho k er w,
      Step (StEval heap env rho (Rgn_App er w) k) Silent
        (StEval heap env rho er (KRgnApp w rho k))
| Step_RgnApp_EvalBody :
    forall heap env' rho' x eb w rho k r,
      find_R w rho = Some r ->
      Step (StReturn heap (Cls (env', rho', Lambda x eb)) (KRgnApp w rho k)) Silent
        (StEval heap env' (update_R (x, r) rho') eb k)
| Step_EffApp_EvalFun :
    forall heap env rho k ef ea,
      Step (StEval heap env rho (Eff_App ef ea) k) Silent
        (StEval heap env rho ef (KEffAppFun ea env rho k))
| Step_EffApp_EvalArg :
    forall heap env rho k ea env' rho' f x ec ee,
      Step (StReturn heap (Cls (env', rho', Mu f x ec ee)) (KEffAppFun ea env rho k)) Silent
        (StEval heap env rho ea (KEffAppArg env' rho' f x ec ee k))
| Step_EffApp_EvalBody :
    forall heap v env' rho' f x ec ee k,
      Step (StReturn heap v (KEffAppArg env' rho' f x ec ee k)) Silent
        (StEval heap
          (update_rec_E (f, Cls (env', rho', Mu f x ec ee)) (x, v) env')
          rho' ee k)
| Step_PairPar_EvalEff1 :
    forall heap env rho k ef1 ea1 ef2 ea2,
      Step (StEval heap env rho (Pair_Par ef1 ea1 ef2 ea2) k) Silent
        (StEval heap env rho (Eff_App ef1 ea1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho k))
| Step_PairPar_EvalEff2 :
    forall heap env rho k ef1 ea1 ef2 ea2 theta1,
      Step
        (StReturn heap (Eff theta1)
          (KPairParEff1 ef1 ea1 ef2 ea2 env rho k)) Silent
        (StEval heap env rho (Eff_App ef2 ea2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k))
| Step_PairPar_EvalMu1 :
    forall heap env rho k ef1 ea1 ef2 ea2 theta1 theta2,
      Disjointness theta1 theta2 ->
      ~ Conflictness theta1 theta2 ->
      Step
        (StReturn heap (Eff theta2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)) Silent
        (StEval heap env rho (Mu_App ef1 ea1)
          (KPairParMu1 ef2 ea2 env rho k))
| Step_PairPar_FallbackMu1 :
    forall heap env rho k ef1 ea1 ef2 ea2 theta1 theta2,
      ~ (Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2) ->
      Step
        (StReturn heap (Eff theta2)
          (KPairParEff2 ef1 ea1 ef2 ea2 env rho theta1 k)) Silent
        (StEval heap env rho (Mu_App ef1 ea1)
          (KPairParMu1 ef2 ea2 env rho k))
| Step_PairPar_EvalMu2 :
    forall heap env rho k ef2 ea2 v1,
      Step (StReturn heap v1 (KPairParMu1 ef2 ea2 env rho k)) Silent
        (StEval heap env rho (Mu_App ef2 ea2) (KPairParMu2 v1 k))
| Step_PairPar_Done :
    forall heap k v1 v2,
      Step (StReturn heap v2 (KPairParMu2 v1 k)) Silent
        (StReturn heap (Pair (v1, v2)) k)
| Step_Cond_EvalGuard :
    forall heap env rho k e et ef,
      Step (StEval heap env rho (Cond e et ef) k) Silent
        (StEval heap env rho e (KCond et ef env rho k))
| Step_Cond_True :
    forall heap env rho k et ef,
      Step (StReturn heap (Bit true) (KCond et ef env rho k)) Silent
        (StEval heap env rho et k)
| Step_Cond_False :
    forall heap env rho k et ef,
      Step (StReturn heap (Bit false) (KCond et ef env rho k)) Silent
        (StEval heap env rho ef k)
| Step_Ref_EvalArg :
    forall heap env rho k w e,
      Step (StEval heap env rho (Ref w e) k) Silent
        (StEval heap env rho e (KRef w rho k))
| Step_Ref_Done :
    forall heap rho k w v r l,
      find_R w rho = Some r ->
      allocate_H heap r = l ->
      Step (StReturn heap v (KRef w rho k)) (Act (DA_Alloc r l v))
        (StReturn (update_H ((r, l), v) heap) (Loc (Rgn_Const true false r) l) k)
| Step_DeRef_EvalArg :
    forall heap env rho k w e,
      Step (StEval heap env rho (DeRef w e) k) Silent
        (StEval heap env rho e (KDeRef w rho k))
| Step_DeRef_Done :
    forall heap rho k w l r v,
      find_R w rho = Some r ->
      find_H (r, l) heap = Some v ->
      Step (StReturn heap (Loc w l) (KDeRef w rho k)) (Act (DA_Read r l v))
        (StReturn heap v k)
| Step_Assign_EvalLoc :
    forall heap env rho k w ea ev,
      Step (StEval heap env rho (Assign w ea ev) k) Silent
        (StEval heap env rho ea (KAssignLoc w ev env rho k))
| Step_Assign_EvalVal :
    forall heap env rho k w ev l,
      Step (StReturn heap (Loc w l) (KAssignLoc w ev env rho k)) Silent
        (StEval heap env rho ev (KAssignVal w l rho k))
| Step_Assign_Done :
    forall heap rho k w l r v,
      find_R w rho = Some r ->
      find_H (r, l) heap <> None ->
      Step (StReturn heap v (KAssignVal w l rho k)) (Act (DA_Write r l v))
        (StReturn (update_H ((r, l), v) heap) Unit k)
| Step_Plus_EvalLeft :
    forall heap env rho k e1 e2,
      Step (StEval heap env rho (Plus e1 e2) k) Silent
        (StEval heap env rho e1 (KPlusL e2 env rho k))
| Step_Plus_EvalRight :
    forall heap env rho k e2 n,
      Step (StReturn heap (Num n) (KPlusL e2 env rho k)) Silent
        (StEval heap env rho e2 (KPlusR n k))
| Step_Plus_Done :
    forall heap k n1 n2,
      Step (StReturn heap (Num n2) (KPlusR n1 k)) Silent
        (StReturn heap (Num (n1 + n2)) k)
| Step_Minus_EvalLeft :
    forall heap env rho k e1 e2,
      Step (StEval heap env rho (Minus e1 e2) k) Silent
        (StEval heap env rho e1 (KMinusL e2 env rho k))
| Step_Minus_EvalRight :
    forall heap env rho k e2 n,
      Step (StReturn heap (Num n) (KMinusL e2 env rho k)) Silent
        (StEval heap env rho e2 (KMinusR n k))
| Step_Minus_Done :
    forall heap k n1 n2,
      Step (StReturn heap (Num n2) (KMinusR n1 k)) Silent
        (StReturn heap (Num (n1 - n2)) k)
| Step_Times_EvalLeft :
    forall heap env rho k e1 e2,
      Step (StEval heap env rho (Times e1 e2) k) Silent
        (StEval heap env rho e1 (KTimesL e2 env rho k))
| Step_Times_EvalRight :
    forall heap env rho k e2 n,
      Step (StReturn heap (Num n) (KTimesL e2 env rho k)) Silent
        (StEval heap env rho e2 (KTimesR n k))
| Step_Times_Done :
    forall heap k n1 n2,
      Step (StReturn heap (Num n2) (KTimesR n1 k)) Silent
        (StReturn heap (Num (n1 * n2)) k)
| Step_Eq_EvalLeft :
    forall heap env rho k e1 e2,
      Step (StEval heap env rho (Eq e1 e2) k) Silent
        (StEval heap env rho e1 (KEqL e2 env rho k))
| Step_Eq_EvalRight :
    forall heap env rho k e2 n,
      Step (StReturn heap (Num n) (KEqL e2 env rho k)) Silent
        (StEval heap env rho e2 (KEqR n k))
| Step_Eq_Done :
    forall heap k n1 n2,
      Step (StReturn heap (Num n2) (KEqR n1 k)) Silent
        (StReturn heap (Bit (Nat.eqb n1 n2)) k)
| Step_AllocAbs :
    forall heap env rho k w r,
      find_R w rho = Some r ->
      Step (StEval heap env rho (AllocAbs w) k) Silent
        (StReturn heap (Eff (Some (singleton_set (CA_AllocAbs r)))) k)
| Step_ReadAbs :
    forall heap env rho k w r,
      find_R w rho = Some r ->
      Step (StEval heap env rho (ReadAbs w) k) Silent
        (StReturn heap (Eff (Some (singleton_set (CA_ReadAbs r)))) k)
| Step_WriteAbs :
    forall heap env rho k w r,
      find_R w rho = Some r ->
      Step (StEval heap env rho (WriteAbs w) k) Silent
        (StReturn heap (Eff (Some (singleton_set (CA_WriteAbs r)))) k)
| Step_ReadConc_EvalArg :
    forall heap env rho k e,
      Step (StEval heap env rho (ReadConc e) k) Silent
        (StEval heap env rho e (KReadConc k))
| Step_ReadConc_Done :
    forall heap k r l,
      Step (StReturn heap (Loc (Rgn_Const true false r) l) (KReadConc k)) Silent
        (StReturn heap (Eff (Some (singleton_set (CA_ReadConc r l)))) k)
| Step_WriteConc_EvalArg :
    forall heap env rho k e,
      Step (StEval heap env rho (WriteConc e) k) Silent
        (StEval heap env rho e (KWriteConc k))
| Step_WriteConc_Done :
    forall heap k r l,
      Step (StReturn heap (Loc (Rgn_Const true false r) l) (KWriteConc k)) Silent
        (StReturn heap (Eff (Some (singleton_set (CA_WriteConc r l)))) k)
| Step_Concat_EvalLeft :
    forall heap env rho k e1 e2,
      Step (StEval heap env rho (Concat e1 e2) k) Silent
        (StEval heap env rho e1 (KConcatL e2 env rho k))
| Step_Concat_EvalRight :
    forall heap env rho k e2 theta,
      Step (StReturn heap (Eff theta) (KConcatL e2 env rho k)) Silent
        (StEval heap env rho e2 (KConcatR theta k))
| Step_Concat_Done :
    forall heap k theta1 theta2,
      Step (StReturn heap (Eff theta2) (KConcatR theta1 k)) Silent
        (StReturn heap (Eff (Union_Theta theta1 theta2)) k)
| Step_Top :
    forall heap env rho k,
      Step (StEval heap env rho Top k) Silent
        (StReturn heap (Eff None) k)
| Step_Empty :
    forall heap env rho k,
      Step (StEval heap env rho Empty k) Silent
        (StReturn heap (Eff (Some empty_set)) k)
| Step_Done :
    forall heap v,
      Step (StReturn heap v KDone) Silent (StDone heap v).

Inductive Steps : State -> Trace -> State -> Prop :=
| Steps_Refl :
    forall state,
      Steps state nil state
| Steps_Step :
    forall state label state' trace state'',
      Step state label state' ->
      Steps state' trace state'' ->
      Steps state (label_trace label ++ trace) state''.
