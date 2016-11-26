Add LoadPath "." as Top.
Require Import Top.Definitions.
Require Import Top.Heap.

Axiom Phi_Seq_Nil_L : forall phi, Phi_Seq Phi_Nil phi = phi.
Axiom Phi_Seq_Nil_R : forall phi, Phi_Seq phi Phi_Nil = phi.
Axiom Phi_Par_Nil_R : forall phi, Phi_Par phi Phi_Nil = phi.
Axiom Phi_Par_Nil_L : forall phi, Phi_Par Phi_Nil phi = phi.

Axiom EquivalenceUpToPermutations:
  forall (h h' h_: Heap) env rho exp v p,
    H.Equal h' h_ -> (* assume we can prove this for an hypothetical heap:=h_ *)
    H.Equal h h'  -> (* read only p *)
    (h, env, rho, exp) ⇓ (h', v, p) ->
    h' = h_.

Axiom ReadOnlyWalkSameHeap:
  forall acts_mu1 acts_mu2 h same_h,
    ReadOnlyPhi (Phi_Par acts_mu1 acts_mu2) ->
    (Phi_Par acts_mu1 acts_mu2, h) ==>* (Phi_Nil, same_h) ->
    H.Equal h same_h.

Axiom UnionTcHeap:
  forall hp' heap_mu1 heap_mu2 sttym sttya,
    H.Equal hp' (Functional_Map_Union_Heap heap_mu1 heap_mu2) ->
    TcHeap (heap_mu1, sttym) ->
    TcHeap (heap_mu2, sttya) ->
    TcHeap (hp', Functional_Map_Union sttya sttym).

Axiom UnionStoreTyping:
  forall l sttya sttym t', 
    ST.find (elt:=tau) l sttya = Some t' -> 
    ST.find (elt:=tau) l sttym = Some t' ->
    ST.find (elt:=tau) l (Functional_Map_Union sttya sttym) = Some t'.