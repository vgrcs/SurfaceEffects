From Stdlib Require Import String.

Require Export theories.SmallStep.Core.Effects.

Inductive Expr :=
| EConst : nat -> Expr
| EBool : bool -> Expr
| EVar : VarId -> Expr
| EMu : VarId -> VarId -> Expr -> Expr -> Expr
| ELambdaRgn : VarId -> Expr -> Expr
| EMuApp : Expr -> Expr -> Expr
| ERgnApp : Expr -> RegionExpr -> Expr
| EEffApp : Expr -> Expr -> Expr
| EPairPar : Expr -> Expr -> Expr
| ECond : Expr -> Expr -> Expr -> Expr
| ERef : RegionExpr -> Expr -> Expr
| EDeref : RegionExpr -> Expr -> Expr
| EAssign : RegionExpr -> Expr -> Expr -> Expr
| EPlus : Expr -> Expr -> Expr
| EMinus : Expr -> Expr -> Expr
| ETimes : Expr -> Expr -> Expr
| EEq : Expr -> Expr -> Expr
| EAllocAbs : RegionExpr -> Expr
| EReadAbs : RegionExpr -> Expr
| EWriteAbs : RegionExpr -> Expr
| EReadConc : Expr -> Expr
| EWriteConc : Expr -> Expr
| EConcat : Expr -> Expr -> Expr
| ETop : Expr
| EEmpty : Expr.
