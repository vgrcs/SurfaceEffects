From stdpp Require Import gmap.
Require Import Ascii.

Definition RgnVal :=  nat.
Definition RgnName := ascii.

Inductive Region : bool * bool * bool -> Set :=
  | Rgn_Const : forall fv bv, RgnVal -> Region (true, fv, bv)
  | Rgn_FVar : forall c bv, RgnName -> Region (c, true, bv)
  | Rgn_BVar : forall c fv, nat -> Region (c, fv, true).
Definition Region_in_Expr := Region (true, true, false).
Definition Region_in_Type := Region (true, true, true).


Definition Rho := gmap RgnName RgnVal.

Definition find_R (k: Region_in_Expr) (m: Rho) : option RgnVal :=
 match k with 
  | Rgn_Const fv bv n => Some n
  | Rgn_FVar c bv n =>  m !! n
  | Rgn_BVar c fv n => None                               
 end.

Definition update_R (p: RgnName * RgnVal) (m : Rho) := <[ (fst p) := (snd p) ]> m.

Definition rho_elem_eq (x y : (RgnName*RgnVal))
  := eqb (fst x) (fst y) = true /\ Nat.eq (snd x) (snd y).

Lemma rho_elem_eq_dec : forall (k k' : RgnName * RgnVal),
    { rho_elem_eq k k' } + { ~ rho_elem_eq k k' }.
Proof.
  intros. unfold rho_elem_eq, Nat.eq. destruct k as (r, l);
    destruct k' as (r', l'); subst; simpl.
  destruct (ascii_dec r r'); destruct (eq_nat_dec l l'). 
  - left. subst.  split;[apply eqb_refl; reflexivity | reflexivity].
  - right. intro. contradict n. intuition.
  - right. intro. destruct H. apply eqb_neq in n.
    rewrite n in H. contradict H. auto.
  - right. intro. destruct H. contradict H. subst. contradiction.
Qed.    


Open Scope char_scope.

Example rho_as_list : list (RgnName*RgnVal)
  := ("i"%char, 0)::("j"%char,1)::[].

Example rho_example : gmap RgnName RgnVal
  := list_to_map rho_as_list.
