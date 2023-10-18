Require Import Definitions.Heap.
Require Import Definitions.Values.
Require Import Definitions.Regions.
Require Import Definitions.Expressions.
Require Import Definitions.DynamicActions.
Require Import Definitions.ComputedActions.
Require Import Definitions.Tactics.
Require Import Coq.Strings.String.


Reserved Notation "e '⇓' n" (at level 50, left associativity).
Inductive BigStep   : (Heap * Env * Rho * Expr) -> (Heap * Val * Phi) -> Prop:=
  | BS_Nat_Cnt    : forall n env rho heap,
                      (heap, env, rho, Const n) ⇓ (heap, Num n, Phi_Nil)
  | BS_Boolean    : forall b env rho heap,
                      (heap, env, rho, Bool b) ⇓ (heap, Bit b, Phi_Nil)                                    
  | BS_Val_Var    : forall x v env rho heap,
                      find_E x env = Some v -> (heap, env, rho, Var x) ⇓ (heap, v, Phi_Nil)                
  | BS_Mu_Abs     : forall f x ec ee env rho (heap fheap : Heap),
                      (heap, env, rho, Mu f x ec ee) ⇓ (heap, Cls (env, rho, Mu f x ec ee), Phi_Nil)
  | BS_Lambda_Abs : forall x eb env rho heap,
                      (heap, env, rho, Lambda x eb) ⇓ (heap, Cls (env, rho, Lambda x eb), Phi_Nil)
  | BS_Mu_App     : forall (f : VarId) x ef ea ec' ee' v v'
                           (env env': Env) (rho rho' : Rho) (heap fheap aheap bheap : Heap) 
                           (facts aacts bacts : Phi),
                      (heap, env, rho, ef) ⇓ (fheap, Cls (env', rho', Mu f x ec' ee'), facts) ->
                      (fheap, env, rho, ea) ⇓ (aheap, v, aacts) ->
                      (aheap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ec') 
                        ⇓ (bheap, v', bacts) -> 
                      (heap, env, rho,  Mu_App ef ea) ⇓ (bheap, v', Phi_Seq (Phi_Seq facts aacts) bacts) 
  | BS_Rgn_App    : forall x er eb w v v'
                           (env env': Env) (rho rho' : Rho) 
                           (heap fheap aheap bheap : Heap) (facts aacts bacts : Phi), 
                      (heap, env, rho, er) ⇓ (fheap, Cls (env', rho', Lambda x eb), facts) ->
                      find_R w rho = Some v' ->
                      (fheap, env', update_R (x, v') rho' , eb) ⇓ (bheap, v, bacts) ->
                      (heap, env, rho, Rgn_App er w) ⇓ (bheap, v, Phi_Seq facts bacts)          
  | BS_Eff_App    : forall (f : VarId) x ef ea ec' ee' v v'  
                           (env env': Env) (rho rho' : Rho) heap (facts aacts bacts : Phi), 
                      (heap, env, rho, ef) ⇓ (heap, Cls (env', rho', Mu f x ec' ee'), facts) ->
                      (heap, env, rho, ea) ⇓ (heap, v', aacts) ->
                      (heap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v') env', rho', ee') 
                        ⇓ (heap, v, bacts) -> 
                      (heap, env, rho, Eff_App ef ea) ⇓ (heap, v, Phi_Seq (Phi_Seq facts aacts) bacts)
  | BS_Pair_Par   : forall env rho ea1 ef1 ea2 ef2 v1 v2 theta1 theta2
                           (heap_eff1 heap_eff2 heap heap_mu1 heap_mu2 heap' : Heap) 
                           (acts_mu1 acts_mu2 acts_eff1 acts_eff2 : Phi),
                      (heap, env, rho, Eff_App ef1 ea1) ⇓ (heap_eff1, Eff theta1, acts_eff1) ->
                      (heap, env, rho, Eff_App ef2 ea2) ⇓ (heap_eff2, Eff theta2, acts_eff2) ->
                      Disjointness theta1 theta2 /\ not (Conflictness theta1 theta2) ->
                      (heap, env, rho, Mu_App ef1 ea1) ⇓ (heap_mu1, v1, acts_mu1) ->
                      (heap, env, rho, Mu_App ef2 ea2) ⇓ (heap_mu2, v2, acts_mu2) ->
                      (Phi_Par acts_mu1 acts_mu2, heap) ==>* (Phi_Nil, heap') ->
                      (heap, env, rho, Pair_Par ef1 ea1 ef2 ea2) 
                        ⇓ (heap', Pair (v1, v2), Phi_Seq (Phi_Par acts_eff1 acts_eff2) (Phi_Par acts_mu1 acts_mu2))
  | BS_Cond_True  : forall e et ef env rho v (heap cheap theap : Heap) (cacts tacts : Phi),
                      (heap, env, rho, e) ⇓ (cheap, (Bit true), cacts) -> 
                      (cheap, env, rho, et) ⇓ (theap, v, tacts) -> 
                      (heap, env, rho, Cond e et ef) ⇓ (theap, v, Phi_Seq cacts tacts)
  | BS_Cond_False : forall e et ef env rho v (heap cheap fheap : Heap) (cacts facts : Phi),
                      (heap, env, rho, e) ⇓ (cheap, (Bit false), cacts) -> 
                      (cheap, env, rho, ef) ⇓ (fheap, v, facts) -> 
                      (heap, env, rho, Cond e et ef) ⇓ (fheap, v, Phi_Seq cacts facts) 
  | BS_New_Ref     : forall e w r l v env rho  (heap heap' : Heap) vacts,
                       (heap, env, rho, e) ⇓ (heap', v, vacts) ->
                       find_R w rho = Some r ->
                       (*find_H (r, l) heap' = None -> *)
                       allocate_H heap' r = l ->
                       (heap, env, rho, Ref w e) ⇓ (update_H ((r, l), v) heap',
                                                    Loc (Rgn2_Const true false r) l,
                                                    Phi_Seq vacts (Phi_Elem (DA_Alloc r l v)))   
  | BS_Get_Ref     : forall ea w r l v env rho (heap heap' : Heap) aacts,
                       (heap, env, rho, ea) ⇓ (heap', Loc w l, aacts) ->
                       find_R w rho = Some r ->
                       find_H (r, l) heap' = Some v ->                       
                       (heap, env, rho, DeRef w ea) ⇓ (heap', v, Phi_Seq aacts (Phi_Elem (DA_Read r l v)))
  | BS_Set_Ref     : forall ea ev w r l v env rho (heap heap' heap'' : Heap) (aacts vacts : Phi),
                       (heap, env, rho, ea) ⇓ (heap', Loc w l, aacts) ->
                       (heap', env, rho, ev) ⇓ (heap'', v, vacts) ->
                       find_R w rho = Some r ->
                       (heap, env, rho, Assign w ea ev) ⇓ (update_H ((r, l), v) heap'', Unit,
                                                           Phi_Seq (Phi_Seq aacts vacts) (Phi_Elem (DA_Write r l v)))
  | BS_Nat_Plus    : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                       (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                       (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) ->  
                       (heap, env, rho, Plus a b) ⇓ (rheap, Num (va + vb), Phi_Seq lacts racts)
  | BS_Nat_Minus   : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                       (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                       (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) ->  
                       (heap, env, rho, Minus a b) ⇓ (rheap, Num (va - vb), Phi_Seq lacts racts)
  | BS_Nat_Times   : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                       (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                       (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) -> 
                       (heap, env, rho, Times a b) ⇓ (rheap, Num (va * vb), Phi_Seq lacts racts)
  | BS_Bool_Eq     : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                       (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                       (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) ->   
                       (heap, env, rho, Eq a b) ⇓ (rheap, Bit (Nat.eqb va vb), Phi_Seq lacts racts)
  | BS_Alloc_Abs   : forall w r env rho heap,
                       find_R w rho = Some r ->
                       (heap, env, rho, AllocAbs w) ⇓ (heap, Eff (Some (singleton_set (CA_AllocAbs r))), Phi_Nil)
  | BS_Read_Abs    : forall w r env rho heap,
                       find_R w rho = Some r ->  
                       (heap, env, rho, ReadAbs w) ⇓ (heap, Eff (Some (singleton_set (CA_ReadAbs r))), Phi_Nil)        
  | BS_Write_Abs   : forall w r env rho heap,
                       find_R w rho = Some r ->   
                       (heap, env, rho, WriteAbs w) ⇓ (heap, Eff (Some (singleton_set (CA_WriteAbs r))), Phi_Nil)
  | BS_Read_Conc   : forall ea r l env rho (heap heap' : Heap) aacts,
                       (heap, env, rho, ea) ⇓ (heap', Loc (Rgn2_Const true false r) l, aacts) ->
                       aacts = Phi_Nil->
                       (heap, env, rho, ReadConc ea) ⇓ (heap', Eff (Some (singleton_set (CA_ReadConc r l))), Phi_Nil) 
  | BS_Write_Conc  : forall ea r l env rho (heap heap' : Heap) aacts,
                       (heap, env, rho, ea) ⇓ (heap', Loc (Rgn2_Const true false r) l, aacts) ->
                       aacts = Phi_Nil ->
                       (heap, env, rho, WriteConc ea) ⇓ (heap', Eff (Some (singleton_set (CA_WriteConc r l))), Phi_Nil)
  | BS_Eff_Concat  : forall a b env rho heap (effa effb : Theta) phia phib,
                       (heap, env, rho, a) ⇓ (heap, Eff effa, phia) ->
                       (heap, env, rho, b) ⇓ (heap, Eff effb, phib) ->
                       (heap, env, rho, Concat a b) ⇓ (heap, Eff (Union_Theta effa effb), Phi_Seq phia phib)
  | BS_Eff_Top     : forall env rho heap,
                       (heap, env, rho, Top) ⇓ (heap, Eff None, Phi_Nil)
  | BS_Eff_Empty   : forall  env rho heap,
                       (heap, env, rho, Empty) ⇓ (heap, Eff (Some empty_set), Phi_Nil)    
where "e '⇓' n" := (BigStep e n) : type_scope.

Tactic Notation "dynamic_cases" tactic (first) ident(c) :=
  first;
  [ Case_aux c "cnt n"
  | Case_aux c "bool b"           
  | Case_aux c "var x"
  | Case_aux c "mu_abs"
  | Case_aux c "rgn_abs"              
  | Case_aux c "mu_app"
  | Case_aux c "rgn_app"             
  | Case_aux c "eff_app"
  | Case_aux c "par_pair"             
  | Case_aux c "cond_true" 
  | Case_aux c "cond_false"
  | Case_aux c "new_ref e"
  | Case_aux c "get_ref e"
  | Case_aux c "set_ref e1 e2"
  | Case_aux c "nat_plus x y"
  | Case_aux c "nat_minus x y"
  | Case_aux c "nat_times x y"
  | Case_aux c "bool_eq x y"
  | Case_aux c "alloc_abs"
  | Case_aux c "read_abs"             
  | Case_aux c "write_abs"             
  | Case_aux c "read_conc"
  | Case_aux c "write_conc"
  | Case_aux c "eff_concat"
  | Case_aux c "eff_top"
  | Case_aux c "eff_empty"
  (*| Case_aux c "mu_rec"*) ].
