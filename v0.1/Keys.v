Require Import Ascii String.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.DecidableTypeEx.
Require Import Coq.ZArith.Znat.
Require Import Coq.Arith.Peano_dec.

Module Type IndexedType.
  Variable t: Type.
  Variable index: t -> nat.
  Hypothesis index_inj: forall (x y: t), index x = index y <-> x = y.
  Variable eq: forall (x y: t), {x = y} + {x <> y}.
End IndexedType.


Module IndexedAscii <: IndexedType.

Definition t := ascii.
Definition index := nat_of_ascii.
Definition eq := ascii_dec.
Hypothesis index_inj: forall (x y: t), index x = index y <-> x = y.

End IndexedAscii.

Module OrderedAscii(A: IndexedType) <: OrderedType.

Definition t := A.t.
Definition eq (x y: t) := x = y.
Definition lt (x y: t) := lt (A.index x) (A.index y).

Lemma eq_refl : forall x : t, eq x x.
Proof (@refl_equal t). 
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof (@sym_equal t).
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof (@trans_equal t).

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
  unfold lt; intros. rewrite <- H in H0. exact H0. 
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
  unfold lt; unfold eq; intros.
  red. intro. subst y. generalize dependent H. apply lt_irrefl.
Qed.

Lemma compare : forall x y : t, Compare lt eq x y.
Proof.
  intros. 
  case_eq ( nat_compare (A.index x) (A.index y)); intro.
  - apply EQ. apply nat_compare_eq in H. apply A.index_inj. assumption.
  - apply LT. apply nat_compare_lt in H. unfold lt. assumption.
  - apply GT. apply nat_compare_gt in H. unfold lt. intuition.
Qed.

Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }.
Proof.
  intros. case_eq (nat_compare (A.index x) (A.index y)); intros.
  - left. apply nat_compare_eq in H. apply A.index_inj. assumption.
  - right. red. intro. inversion H0. apply nat_compare_lt in H. apply A.index_inj in H1. 
    intuition.
  - right. red. intro. inversion H0. apply nat_compare_gt in H. apply A.index_inj in H1. 
    intuition.
Defined.

End OrderedAscii.

Module AsciiVars := OrderedAscii (IndexedAscii).

Module RegionVars := PairOrderedType Nat_as_OT Nat_as_OT.