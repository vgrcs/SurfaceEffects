Require Import Definitions.Regions.
Require Import Definitions.Keys.
Require Import Ascii.

Definition VarId := ascii.

Inductive Expr :=
  | Const     : nat -> Expr
  | Bool      : bool -> Expr
  | Var       : VarId -> Expr
  | Mu        : VarId -> VarId -> Expr -> Expr -> Expr
  | Lambda    : VarId -> Expr -> Expr                                               
  | Mu_App    : Expr -> Expr -> Expr 
  | Rgn_App   : Expr -> Region_in_Expr -> Expr                                     
  | Eff_App   : Expr -> Expr -> Expr
  | Pair_Par  : Expr -> Expr -> Expr -> Expr -> Expr                              
  | Cond      : Expr -> Expr -> Expr -> Expr 
  | Ref       : Region_in_Expr -> Expr -> Expr                  
  | DeRef     : Region_in_Expr -> Expr -> Expr                     
  | Assign    : Region_in_Expr -> Expr -> Expr -> Expr
  | Plus      : Expr -> Expr -> Expr
  | Minus     : Expr -> Expr -> Expr
  | Times     : Expr -> Expr -> Expr
  | Eq        : Expr -> Expr -> Expr
  | AllocAbs  : Region_in_Expr -> Expr                         
  | ReadAbs   : Region_in_Expr -> Expr
  | WriteAbs  : Region_in_Expr -> Expr                               
  | ReadConc  : Expr -> Expr               
  | WriteConc : Expr -> Expr
  | Concat    : Expr -> Expr -> Expr
  | Top       : Expr
  | Empty     : Expr. 
Notation "'(|' a b ',' c d '|)" := (Pair_Par a b c d) (at level 60).

Inductive ParallelExpr : Expr -> Prop :=
  | ParExpr : forall ef1 ea1 ef2 ea2, 
                ParallelExpr (Pair_Par ef1 ea1 ef2 ea2). 
