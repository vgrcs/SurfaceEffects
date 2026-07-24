From Stdlib Require Import String.

Require Export theories.NewSmallStep.Core.Effects.

Inductive NExpr :=
| EConst : nat -> NExpr
| EBool : bool -> NExpr
| EVar : VarId -> NExpr
| EMu : VarId -> VarId -> NExpr -> NExpr -> NExpr
| ELambdaRgn : VarId -> NExpr -> NExpr
| EMuApp : NExpr -> NExpr -> NExpr
| ERgnApp : NExpr -> RegionExpr -> NExpr
| EEffApp : NExpr -> NExpr -> NExpr
| ECond : NExpr -> NExpr -> NExpr -> NExpr
| ERef : RegionExpr -> NExpr -> NExpr
| EDeref : RegionExpr -> NExpr -> NExpr
| EAssign : RegionExpr -> NExpr -> NExpr -> NExpr
| EPlus : NExpr -> NExpr -> NExpr
| EMinus : NExpr -> NExpr -> NExpr
| ETimes : NExpr -> NExpr -> NExpr
| EEq : NExpr -> NExpr -> NExpr
| EAllocAbs : RegionExpr -> NExpr
| EReadAbs : RegionExpr -> NExpr
| EWriteAbs : RegionExpr -> NExpr
| EReadConc : NExpr -> NExpr
| EWriteConc : NExpr -> NExpr
| EConcat : NExpr -> NExpr -> NExpr
| ETop : NExpr
| EEmpty : NExpr.
