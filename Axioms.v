Add LoadPath "." as Top.
Require Import Top.Definitions.

Axiom Phi_Seq_Nil_L : forall phi, Phi_Seq Phi_Nil phi = phi.
Axiom Phi_Seq_Nil_R : forall phi, Phi_Seq phi Phi_Nil = phi.
Axiom Phi_Par_Nil_R : forall phi, Phi_Par phi Phi_Nil = phi.
Axiom Phi_Par_Nil_L : forall phi, Phi_Par Phi_Nil phi = phi.

Axiom DeterminismUpToPermutations:
  forall (h h' h_: Heap) env rho exp v p,
    H.Equal h' h_ -> (* assume we can prove this for an hypothetical heap:=h_ *)
    H.Equal h h'  -> (* read only p *)
    (h, env, rho, exp) ⇓ (h', v, p) ->
    h' = h_.

