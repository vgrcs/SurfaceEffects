Add LoadPath "." as Top.
Require Import Top.Definitions.
Require Import Top.Heap.
Require Import Top.Keys.

Axiom Phi_Seq_Nil_L : forall phi, Phi_Seq Phi_Nil phi = phi.
Axiom Phi_Seq_Nil_R : forall phi, Phi_Seq phi Phi_Nil = phi.
Axiom Phi_Par_Nil_R : forall phi, Phi_Par phi Phi_Nil = phi.
Axiom Phi_Par_Nil_L : forall phi, Phi_Par Phi_Nil phi = phi.

Axiom EvaluationMuAppIncludesEffectEvaluation:
  forall h'' env rho ef fheap env' rho' f x ec' ee' facts ea aheap v v' aacts h' bacts e eacts, 
    (h'', env, rho, ef) ⇓ (fheap, Cls (env', rho', Mu f x ec' ee'), facts) ->
    (fheap, env, rho, ea) ⇓ (aheap, v, aacts) ->
    (aheap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', 
            rho', ec') ⇓ (h', v', bacts)->
    (aheap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', 
            rho', ee') ⇓ (aheap, e, eacts).

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


Axiom fold_subst_rgn_left_1:
  forall this1 k e this2 t x this1_is_bst,
    R.Raw.bst (R.Raw.Node this1 k e this2 t) ->
    R.Raw.In x this2 ->
    (fold_subst_rgn {| R.this := this1; R.is_bst := this1_is_bst |} (Rgn2_FVar true true x) = 
     Rgn2_FVar true true x).

Axiom fold_subst_rgn_left_2:
  forall this1 k (e : nat) this2 (t : Int.Z_as_Int.t) x v  is_bst_,
    R.MapsTo x v {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := is_bst_ |} ->
    R.Raw.In x this2 ->
    AsciiVars.lt k x.

Axiom fold_subst_rgn_eq_1:
  forall k this1 (e:nat) this2 (t : Int.Z_as_Int.t) (b:R.Raw.bst (R.Raw.Node this1 k e this2 t)),
    R.Raw.find k (R.this {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := b|}) = Some e ->
    fold_subst_rgn {| R.this := R.Raw.Node this1 k e this2 t; R.is_bst := b|} (Rgn2_FVar true true k) 
    = Rgn2_Const true true e.

Axiom subst_rho_eps_aux_1 :
 forall rho rho' n x e e1 sa sa'',
   fold_subst_eps rho e1 = fold_subst_eps rho' (closing_rgn_in_eps2 n x e) ->
   fold_subst_sa rho sa = fold_subst_sa rho' (closing_rgn_in_sa2 n x sa'') /\ e1 sa /\ e sa''.

Axiom subst_rho_eps_aux_2:
  forall e e1 sa' n x rho rho',
    lc_type_eps e ->
    lc_type_sa sa' ->
    fold_subst_eps rho e1 = fold_subst_eps rho' (closing_rgn_in_eps2 n x e) ->
    fold_subst_sa rho sa' = fold_subst_sa rho' (closing_rgn_in_sa2 n x sa').