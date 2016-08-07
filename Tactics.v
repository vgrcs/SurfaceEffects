(* begin hide *)
Require String. 

Open Scope string_scope.
Open Scope list_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
(* end hide *)


(* ********** *)
(* ********** *)

(* "clear_except H" is like "clear - H",
 * but clears even in the presence of goals with meta-variables.
 *)
Ltac clear_except H :=
  repeat match goal with
           | [ H' : _ |- _ ] =>
             progress (match H' with
                         | H => idtac
                         | _ => clear H'
                       end)
         end.

(* ********** *)

Tactic Notation "dup" hyp(H1) "as" ident(H2) :=
  let P := type of H1 in
  assert P as H2 by exact H1.

Tactic Notation "dup" hyp(H1) :=
  let P := type of H1 in
  assert P by exact H1.

(* ********** *)

Ltac with_hyp P f :=
  match goal with
    | [ H : P |- _ ] => f H
    | [ H : eq _ _ |- _ ] =>
      let TEMP := fresh in
      assert P as TEMP by simple apply H; clear TEMP; f H
  end.

Ltac with_dup_hyp P f :=
  let TEMP := fresh in
  with_hyp P ltac:(fun H => dup H as TEMP; f TEMP).

Tactic Notation "derived" constr(P) :=
  with_hyp P ltac:(fun H => clear_except H ; exact H).
