(*From stdpp Require Import fin_maps fin_map_dom.
From stdpp Require Import strings pmap *)
From stdpp Require Import gmap.

From Coq Require Import Ascii.
Require Import Top0.Keys.
Require Import Coq.FSets.FMapAVL.
Module E := FMapAVL.Make (AsciiVars).

Open Scope char_scope.


Lemma Test:
  {[ "x":=3]} =@{gmap Ascii.ascii nat} ∅.
Admitted.  

Close Scope char_scope.
