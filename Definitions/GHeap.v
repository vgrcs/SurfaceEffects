From stdpp Require Import gmap.
Require Import Top0.Values.

Definition Heap := gmap (prod nat nat) Val.


(*
-- Function to merge two sorted lists (heaps)
type AddressValue = (Int, Int)  -- (Address, Value)

merge :: [AddressValue] -> [AddressValue] -> [AddressValue]
merge [] heap = heap
merge heap [] = heap
merge h1@((a1, v1):rest1) h2@((a2, v2):rest2)
  | a1 < a2   = (a1, v1) : merge rest1 h2
  | otherwise = (a2, v2) : merge h1 rest2
*)
