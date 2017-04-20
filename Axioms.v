Add LoadPath "." as Top0.
Require Import Top0.Definitions.
Require Import Top0.Heap.
Require Import Top0.Keys.
Require Import Top0.Nameless.
Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.

(* Use these as constructors inside "Inductive Phi" *)
Axiom Phi_Seq_Nil_L : forall phi, Phi_Seq Phi_Nil phi = phi.
Axiom Phi_Seq_Nil_R : forall phi, Phi_Seq phi Phi_Nil = phi.
Axiom Phi_Par_Nil_R : forall phi, Phi_Par phi Phi_Nil = phi.
Axiom Phi_Par_Nil_L : forall phi, Phi_Par Phi_Nil phi = phi.

 (* both ec' and ee' and evaluated with the same context, but twice: inside Bs_Mu_App and BS_EffApp*)
Axiom MuAppAndEffAppShareArgument:
 forall h'' env rho ef env' rho' f x ec' ee' ea aheap v eff facts1 aacts1 bacts1, 
   (forall fheap h' bacts facts v' aacts, 
      (h'', env, rho, ef) ⇓ (fheap, Cls (env', rho', Mu f x ec' ee'), facts) ->
      (fheap, env, rho, ea) ⇓ (aheap, v, aacts) ->
      (aheap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ec') ⇓ (h', v', bacts) ->
      (h'', env, rho, Mu_App ef ea) ⇓ (h', v', Phi_Seq (Phi_Seq facts aacts)bacts)) -> 
   (* above is the definition of the type constructor BS_Mu_App *)
   (h'', env, rho, Eff_App ef ea) ⇓ (h'', eff, Phi_Seq (Phi_Seq facts1 aacts1) bacts1) ->
   (aheap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ee') ⇓ (h'', eff, bacts1). 
  
(* Assuming that MuAppIncludesEffectShareArgument is a "specification", this prove the necessary goal *)
Lemma EvaluationEffectFromEffApp:
 forall h'' env rho ef env' rho' f x ec' ee' ea aheap v eff facts1 aacts1 bacts1,
   (h'', env, rho, Eff_App ef ea) ⇓ (h'', eff, Phi_Seq (Phi_Seq facts1 aacts1) bacts1) ->
   (aheap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ee') ⇓ (h'', eff, bacts1).
Proof.
  intros.
  inversion H using MuAppAndEffAppShareArgument.
  intros. econstructor; eauto.
Qed. 

(* Inside "BigStep" we still don't use "E.Equal" to pass around heaps. 
   We need to resort to Coq equality when doing the proof for PairPar *)  
Axiom ReadOnlyWalkSameHeap:
  forall acts_mu1 acts_mu2 h same_h,
    ReadOnlyPhi (Phi_Par acts_mu1 acts_mu2) ->
    (Phi_Par acts_mu1 acts_mu2, h) ==>* (Phi_Nil, same_h) ->
    (*H.Equal h same_h.*)
    h = same_h.

(* Induction principle for TcHeap when we know that previous heaps are 
   consistent and the new ones are non-overlapping. *)
Axiom UnionTcHeap:
  forall hp hp' ef1 ea1 ef2 ea2 theta1 theta2 v1 v2 acts_eff1 acts_eff2 env rho
         heap heap_mu1 heap_mu2 heap_eff1 heap_eff2 sttym sttya acts_mu1 acts_mu2,
    (heap, env, rho, Eff_App ef1 ea1) ⇓ (heap_eff1, Eff theta1, acts_eff1) ->
    (heap, env, rho, Eff_App ef2 ea2) ⇓ (heap_eff2, Eff theta2, acts_eff2) ->
    Disjointness theta1 theta2 /\ ~ Conflictness theta1 theta2 ->
    (heap, env, rho, Mu_App ef1 ea1) ⇓ (heap_mu1, v1, acts_mu1) ->
    (heap, env, rho, Mu_App ef2 ea2) ⇓ (heap_mu2, v2, acts_mu2) ->
    (Phi_Par acts_mu1 acts_mu2, hp) ==>* (Phi_Nil, hp') ->
    TcHeap (heap_mu1, sttym) ->
    TcHeap (heap_mu2, sttya) ->
    TcHeap (hp', Functional_Map_Union sttya sttym).


Lemma TcValExtended_1 :
  forall stty sttya sttyb v rho ty,
    (forall (l : ST.key) (t' : tau),
       ST.find (elt:=tau) l stty = Some t' -> ST.find (elt:=tau) l sttya = Some t' ) ->
    (forall (l : ST.key) (t' : tau),
       ST.find (elt:=tau) l stty = Some t' -> ST.find (elt:=tau) l sttyb = Some t' ) ->
    TcVal (sttya, v, subst_rho rho ty) ->
    TcVal (Functional_Map_Union sttya sttyb, v, subst_rho rho ty).
Proof.
  intros stty sttya sttyb v rho ty H1 H2 H3.  
  generalize dependent sttyb. 
  generalize dependent stty.
  dependent induction H3; intros; try (solve [rewrite <- x; econstructor]).
  - rewrite <- x. econstructor; eauto.
    admit.
  - rewrite <- x. econstructor; eauto.
    admit.
  - rewrite <- x. econstructor.
    + admit.
    + admit.  
Admitted. 

Axiom TcValExtended_2 :
  forall stty sttya sttyb v rho ty,
    (forall (l : ST.key) (t' : tau),
       ST.find (elt:=tau) l stty = Some t' -> ST.find (elt:=tau) l sttya = Some t' ) ->
    (forall (l : ST.key) (t' : tau),
       ST.find (elt:=tau) l stty = Some t' -> ST.find (elt:=tau) l sttyb = Some t' ) ->
    TcVal (sttyb, v, subst_rho rho ty) ->
    TcVal (Functional_Map_Union sttya sttyb, v, subst_rho rho ty).

Axiom UnionStoreTyping:
  forall l sttya sttym t', 
    ST.find (elt:=tau) l sttya = Some t' -> 
    ST.find (elt:=tau) l sttym = Some t' ->
    ST.find (elt:=tau) l (Functional_Map_Union sttya sttym) = Some t'.

Require Import Coq.Logic.FunctionalExtensionality.
Axiom subst_rho_eps_aux_1 :
 forall rho rho' n x e e1 sa sa',
   lc_type_eps e ->
   lc_type_sa sa' ->
   (fold_subst_eps rho e1) = (fold_subst_eps rho' (closing_rgn_in_eps2 n x e)) ->
   fold_subst_sa rho sa = fold_subst_sa rho' (closing_rgn_in_sa2 n x sa') /\ e1 sa /\ e sa'.
