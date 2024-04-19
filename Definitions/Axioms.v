From stdpp Require Import gmap.
Require Import Definitions.DynamicActions.
Require Import Definitions.Semantics.
Require Import Definitions.Values.
Require Import Definitions.GHeap.
Require Import Definitions.Expressions.
Require Import Definitions.GTypes.
Require Import Definitions.Regions.


(* Use these as constructors inside "Inductive Phi" *)
Axiom Phi_Seq_Nil_L : forall phi, Phi_Seq Phi_Nil phi = phi.
Axiom Phi_Seq_Nil_R : forall phi, Phi_Seq phi Phi_Nil = phi.
Axiom Phi_Par_Nil_R : forall phi, Phi_Par phi Phi_Nil = phi.
Axiom Phi_Par_Nil_L : forall phi, Phi_Par Phi_Nil phi = phi.

(* both ec' and ee' and evaluated with the same context, but twice:
inside Bs_Mu_App and BS_EffApp *)
Axiom MuAppAndEffAppShareArgument:
 forall h'' env rho ef env' rho' f x ec' ee' ea aheap v eff facts1 aacts1 bacts1, 
   (forall fheap h' bacts facts v' aacts phi, 
      (h'', env, rho, ef) ⇓ (fheap, Cls (env', rho', Mu f x ec' ee'), facts) ->
      (fheap, env, rho, ea) ⇓ (aheap, v, aacts) ->
      (aheap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ec')
        ⇓ (h', v', bacts) ->
      phi = Phi_Seq (Phi_Seq facts aacts) bacts ->
      h'' ≡@{Heap} fheap ->
      (h'', env, rho, Mu_App ef ea) ⇓ (h', v', phi)) -> 
   (* above is the definition of the type constructor BS_Mu_App *)
   (h'', env, rho, Eff_App ef ea) ⇓ (h'', eff, Phi_Seq (Phi_Seq facts1 aacts1) bacts1) ->
   (aheap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ee')
     ⇓ (h'', eff, bacts1). 
