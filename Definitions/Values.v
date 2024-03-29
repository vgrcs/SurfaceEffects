From stdpp Require Import gmap.
Require Import Ascii String.
Require Import Definitions.Regions.
Require Import Definitions.Expressions.
Require Import Definitions.ComputedActions.

Inductive Val :=
| Loc  : Region_in_Expr -> nat -> Val
| Num  : nat -> Val
| Bit  : bool -> Val
| Cls  : (gmap VarId Val * Rho * Expr) -> Val
| Eff  : Theta -> Val
| Unit : Val
| Pair : Val * Val -> Val.

Definition Env := gmap VarId Val.

Definition find_E (k: VarId) (m: Env) : option Val := m !! k.

Definition update_E (p: VarId * Val) (m: Env) :=  <[ fst p := snd p ]>  m.

Definition update_rec_E (f : VarId * Val) (x: VarId * Val) m :=
  let m' := update_E f m
  in update_E x m'.


