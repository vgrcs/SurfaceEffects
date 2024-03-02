Require Import Definitions.Regions.
Require Import Definitions.Keys.
Require Import Definitions.Expressions.
Require Import Definitions.ComputedActions.

Module E := FMapAVL.Make (AsciiVars).
Module Raw := E.Raw.


Inductive Val :=
| Loc  : Region_in_Expr -> nat -> Val
| Num  : nat -> Val
| Bit  : bool -> Val
| Cls  : (Raw.t Val * Rho * Expr) -> Val
| Eff  : Theta -> Val
| Unit : Val
| Pair : Val * Val -> Val.


Definition Env := Raw.t Val.
Definition V_Key := Raw.key.


Definition find_E (k: VarId) (m: Env) : option Val := Raw.find (elt := Val) k m. 

Definition update_E (p: VarId * Val) (m : Env) := Raw.add (fst p) (snd p) m.

Definition update_rec_E (f : VarId * Val) (x: VarId * Val) m :=
  let m' := Raw.add (fst f) (snd f) m
  in Raw.add (fst x) (snd x) m'.


