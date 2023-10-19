Require Import Coq.Sets.Ensembles.
Require Import Definitions.Keys.
Require Import Definitions.Regions.
Require Import Definitions.ComputedActions.
Require Import Definitions.StaticActions.
Require Import Definitions.Values.
Require Import Definitions.Expressions.

(* substitute for type *)
Inductive tau :=
  | Ty2_Natural : tau
  | Ty2_Boolean : tau
  | Ty2_Effect  : tau
  | Ty2_Unit    : tau
  | Ty2_Pair    : tau -> tau -> tau
  | Ty2_Ref     : Region_in_Type -> tau -> tau
  | Ty2_Arrow   : tau -> Epsilon -> tau -> Epsilon -> tau -> tau
  | Ty2_ForallRgn : Epsilon -> tau -> tau.


Module ST := FMapAVL.Make (RegionVars).
Definition Sigma : Type := ST.t tau.
Definition Gamma : Type := E.t tau.
Definition Omega : Type := Ensemble VarId.

Definition find_T (k: V_Key) (m: Gamma) : option tau := E.find k m.
Definition update_T (p: V_Key * tau) m := E.add (fst p) (snd p) m.
Definition update_rec_T (f: VarId * tau) (x: VarId * tau) m :=
  let m' := E.add (fst f) (snd f) m
  in E.add (fst x) (snd x) m'.

Definition find_ST (k: ST.key) (m: Sigma) : option tau := ST.find k m.
Definition update_ST (p: ST.key * tau) m := ST.add (fst p) (snd p) m.

Definition Functional_Map_Union (stty1 stty2 : Sigma) : Sigma :=
  let f := fun (k : nat * nat) (v : tau) (m : Sigma) => ST.add k v m
  in ST.fold f stty1 stty2.

Inductive merge_Sigma : Sigma -> Sigma -> Sigma -> Prop :=
| mergeL : forall stty1 stty2, merge_Sigma stty1 stty2 (Functional_Map_Union stty1 stty2)
| mergeR : forall stty1 stty2, merge_Sigma stty1 stty2 (Functional_Map_Union stty2 stty1).


(** begin of free regions **)
Definition free_rgn_vars_in_rgn (rgn: Region_in_Type) : Ensemble VarId :=
  match rgn with
  | Rgn2_Const _ _ _ => empty_set
  | Rgn2_FVar _ _ n => singleton_set n
  | Rgn2_BVar _ _ _ => empty_set
  end.

Definition free_region (rgn: Region_in_Type) : Ensemble VarId := free_rgn_vars_in_rgn rgn.

Definition free_rgn_vars_in_sa (sa: StaticAction) : Ensemble VarId :=
  match sa with
  | SA2_Alloc rgn => free_rgn_vars_in_rgn rgn
  | SA2_Read rgn => free_rgn_vars_in_rgn rgn
  | SA2_Write rgn => free_rgn_vars_in_rgn rgn
  end.


Definition free_rgn_vars_in_eps (eps: Epsilon) : Ensemble VarId := 
  fun n => exists (sa : StaticAction),
             eps sa /\ (free_rgn_vars_in_sa sa) n.


Fixpoint frv (t: tau) : Ensemble VarId :=
  match t with
  | Ty2_Natural    => empty_set
  | Ty2_Boolean    => empty_set
  | Ty2_Effect     => empty_set
  | Ty2_Unit       => empty_set
  | Ty2_Pair t1 t2 => set_union (frv t1) (frv t2)                        
  | Ty2_Ref rgn ty => set_union (free_rgn_vars_in_rgn rgn) (frv ty)
  | Ty2_Arrow aty ceff crty eeff erty =>
                      set_union (frv aty)
                                (set_union (set_union (free_rgn_vars_in_eps ceff)
                                                      (free_rgn_vars_in_eps eeff))
                                           (set_union (frv crty)
                                                      (frv erty)))
  | Ty2_ForallRgn eff rty => set_union (free_rgn_vars_in_eps eff)
                                       (frv rty)                                      
  end.

Fixpoint not_set_elem_frv (t: tau) x : Prop :=
  match t with
    | Ty2_Natural    => True
    | Ty2_Boolean    => True 
    | Ty2_Effect     => True
    | Ty2_Unit       => True
    | Ty2_Pair t1 t2 => (not_set_elem (frv t1) x) /\ (not_set_elem (frv t2) x)  
    | Ty2_Ref rgn ty => (not_set_elem (free_rgn_vars_in_rgn rgn) x) /\ 
                        (not_set_elem (frv ty) x)
    | Ty2_Arrow aty ceff crty eeff erty 
      => (not_set_elem (frv aty) x) /\
         (not_set_elem (free_rgn_vars_in_eps ceff) x) /\
         (not_set_elem (free_rgn_vars_in_eps eeff) x) /\
         (not_set_elem (frv crty) x) /\
         (not_set_elem (frv erty) x)
    | Ty2_ForallRgn eff rty => (not_set_elem (free_rgn_vars_in_eps eff) x) /\
                               (not_set_elem (frv rty) x)
  end.


Notation "x '#' t" := (not_set_elem (frv t) x) (at level 60).


(** locally closed **)
Inductive lc_type_rgn : Region_in_Type -> Prop :=
     | lc_rgn_const : forall r, lc_type_rgn (Rgn2_Const true true r)
     | lc_rgn_fvar  : forall r, lc_type_rgn (Rgn2_FVar true true r).

Inductive lc_type_sa : StaticAction -> Prop :=
     | lc_sa_alloc : forall r, lc_type_rgn (r) -> lc_type_sa (SA2_Alloc r)
     | lc_sa_read  : forall r, lc_type_rgn (r) -> lc_type_sa (SA2_Read r)
     | lc_sa_write : forall r, lc_type_rgn (r) -> lc_type_sa (SA2_Write r).

Inductive lc_type_eps : Epsilon -> Prop :=
     | lc_eps : forall eps, (forall (sa : StaticAction), eps sa /\ lc_type_sa (sa)) ->
                            lc_type_eps (eps).


Definition mk_rgn_type (u: Region_in_Expr) : Region_in_Type
 := match u with
      | Rgn2_Const fv bv n => Rgn2_Const true true n
      | Rgn2_FVar c bv n => Rgn2_FVar true true n
      | Rgn2_BVar c fv n => Rgn2_BVar true true n                              
    end.

Definition lc u := lc_type_rgn (mk_rgn_type u).


(** begin of openings **)
Definition opening_rgn_in_rgn (k : nat) (u: Region_in_Type) (t: Region_in_Type) : Region_in_Type
 := match t with
    | Rgn2_Const _ _ _ => t
    | Rgn2_FVar _ _ _ => t
    | Rgn2_BVar _ _ n => if (Nat.eqb n k) then u else t
    end.

Definition opening_rgn_in_sa (k : nat) (u: Region_in_Type) (sa: StaticAction) : StaticAction :=
  match sa with
  | SA2_Alloc rgn => SA2_Alloc (opening_rgn_in_rgn k u rgn)
  | SA2_Read rgn  => SA2_Read (opening_rgn_in_rgn k u rgn)
  | SA2_Write rgn => SA2_Write (opening_rgn_in_rgn k u rgn)
  end.

Definition opening_rgn_in_eps (k : nat) (u: Region_in_Type) (eps: Epsilon) : Epsilon := 
  fun sa => exists sa', eps sa' /\ opening_rgn_in_sa k u sa' = sa.

Fixpoint opening_rgn_exp (k: nat) (u: Region_in_Type) (t: tau) {struct t} : tau :=
  match t with
  | Ty2_Natural => t
  | Ty2_Boolean => t
  | Ty2_Effect  => t
  | Ty2_Unit    => t                     
  | Ty2_Pair ty1 ty2  =>  Ty2_Pair (opening_rgn_exp k u ty1)  (opening_rgn_exp k u ty2) 
  | Ty2_Ref rgn ty => Ty2_Ref (opening_rgn_in_rgn k u rgn) (opening_rgn_exp k u ty)
  | Ty2_Arrow aty ceff crty eeff erty => Ty2_Arrow (opening_rgn_exp k u aty)
                                                   (opening_rgn_in_eps k u ceff) (opening_rgn_exp k u crty)
                                                   (opening_rgn_in_eps k u eeff) (opening_rgn_exp k u erty)
  | Ty2_ForallRgn eff rty => Ty2_ForallRgn (opening_rgn_in_eps (S k) u eff) (opening_rgn_exp (S k) u rty)
  end.


Definition open_rgn_eff (u: Region_in_Type)  (eps: Epsilon) : Epsilon := opening_rgn_in_eps 0 u eps.
Definition open (u: Region_in_Type)  (t: tau) : tau := opening_rgn_exp 0 u t.
Definition open_var (t : tau) (x : VarId) : tau :=
  let rgn_fvar := Rgn2_FVar true true x
  in opening_rgn_exp 0 (rgn_fvar) t.


(** begin of closings **)
Definition closing_rgn_in_rgn (k : nat) (x: VarId) (t: Region_in_Type) : Region_in_Type
 := match t with
    | Rgn2_Const _ _ _ => t
    | Rgn2_FVar _ _ n  => if AsciiVars.eq_dec n x then (Rgn2_BVar true true k) else t
    | Rgn2_BVar _ _ _  => t
    end.

Definition closing_rgn_in_sa (k : nat) (x: VarId) (sa: StaticAction) : StaticAction :=
  match sa with
  | SA2_Alloc rgn => SA2_Alloc (closing_rgn_in_rgn k x rgn)
  | SA2_Read rgn  => SA2_Read (closing_rgn_in_rgn k x rgn)
  | SA2_Write rgn => SA2_Write (closing_rgn_in_rgn k x rgn)
  end.

Definition closing_rgn_in_eps(k : nat) (x: VarId) (eps: Epsilon) : Epsilon :=
  fun sa => exists sa', eps sa' /\ closing_rgn_in_sa k x sa' = sa.

Fixpoint closing_rgn_exp (k: nat) (x: VarId) (t: tau) {struct t} : tau :=
  match t with
  | Ty2_Natural => t
  | Ty2_Boolean => t
  | Ty2_Effect  => t
  | Ty2_Unit    => t
  | Ty2_Pair t1 t2 => Ty2_Pair  (closing_rgn_exp k x t1) (closing_rgn_exp k x t2)
  | Ty2_Ref rgn ty => Ty2_Ref (closing_rgn_in_rgn k x rgn) (closing_rgn_exp k x ty)
  | Ty2_Arrow aty ceff crty eeff erty => Ty2_Arrow (closing_rgn_exp k x aty)
                                                   (closing_rgn_in_eps k x ceff) (closing_rgn_exp k x crty)
                                                   (closing_rgn_in_eps k x eeff) (closing_rgn_exp k x erty)
  | Ty2_ForallRgn eff rty => Ty2_ForallRgn (closing_rgn_in_eps (S k) x eff) (closing_rgn_exp (S k) x rty)
  end.


Definition close_var (x : VarId) (t : tau) := closing_rgn_exp 0 x t.
Definition close_var_eff (x : VarId) (eps : Epsilon) := closing_rgn_in_eps 0 x eps.
(** end of closings **)



Inductive lc_type : tau -> Prop :=
  | lc_natural : lc_type Ty2_Natural
  | lc_pair    : forall t1 t2,
                   lc_type t1 -> lc_type t2 -> lc_type (Ty2_Pair t1 t2)
  | lc_ref     : forall r t,
                   lc_type_rgn r -> lc_type t -> lc_type (Ty2_Ref r t)
  | lc_arrow   : forall aty ceff crty eeff erty,
                   lc_type aty -> lc_type_eps ceff -> lc_type crty ->
                   lc_type_eps eeff -> lc_type erty ->
                   lc_type (Ty2_Arrow aty ceff crty eeff erty)
  | lc_forall  : forall L eff rty,
                   (forall x, not_set_elem L x -> lc_type (open_var rty x)) ->
                   lc_type_eps eff ->
                   lc_type rty ->
                   lc_type (Ty2_ForallRgn eff rty).
(** end of locally closed **)



Inductive TcRho : (Rho * Omega) -> Prop :=
  | TC_Rho : forall rho rgns,
               (forall r, R.find r rho <> None <-> set_elem rgns r) ->
               TcRho (rho, rgns).

Inductive TcInc : (Gamma * Omega) -> Prop :=
     | Tc_Inc : forall ctxt rgns, 
                  (forall x t, 
                     find_T x ctxt = Some t -> included (frv t) rgns) ->
                  TcInc (ctxt, rgns). 

Inductive TcRgn : (Omega * Region_in_Expr) -> Prop :=
  | TC_Rgn_Const : forall rgns s,
                      TcRgn (rgns, Rgn2_Const true false s)
  | TC_Rgn_Var   : forall rgns r,
                      set_elem rgns r ->
                      TcRgn (rgns, Rgn2_FVar true false r).      



(** begin of substitutions **)
Definition subst_rgn  (z : VarId) (u : Region_in_Expr) (t: Region_in_Type) : Region_in_Type :=
  match t with
    | Rgn2_Const _ _ r => t
    | Rgn2_FVar _ _ r  => if (AsciiVars.eq_dec z r) then mk_rgn_type u else t 
    | Rgn2_BVar _ _ _  => t
  end.

Definition subst_sa (z : VarId) (u : Region_in_Expr) (t: StaticAction) : StaticAction :=
 match t with
  | SA2_Alloc rgn => SA2_Alloc (subst_rgn z u rgn)
  | SA2_Read rgn  => SA2_Read  (subst_rgn z u rgn)
  | SA2_Write rgn => SA2_Write (subst_rgn z u rgn)
 end.

Definition subst_eps  (z : VarId) (u : Region_in_Expr) (t: Epsilon) : Epsilon :=
   fun sa => exists sa', t sa' /\ subst_sa z u sa' = sa.

Reserved Notation "'[' x ':=' u ']' t" (at level 20).
Fixpoint subst_type (z : VarId) (u : Region_in_Expr) (t : tau) {struct t} : tau :=
  match t with
    | Ty2_Natural => Ty2_Natural
    | Ty2_Boolean => Ty2_Boolean
    | Ty2_Effect  => Ty2_Effect
    | Ty2_Unit    => Ty2_Unit
    | Ty2_Pair t1 t2  => Ty2_Pair (subst_type z u t1) (subst_type z u t2)                      
    | Ty2_Ref r t => Ty2_Ref (subst_rgn z u r) (subst_type z u t)
    | Ty2_Arrow aty ceff crty eeff erty => Ty2_Arrow (subst_type z u aty) (subst_eps z u ceff) (subst_type z u crty)
                                                     (subst_eps z u eeff) (subst_type z u erty)
    | Ty2_ForallRgn eff rty => Ty2_ForallRgn (subst_eps z u eff) (subst_type z u rty)
  end
where "'[' x ':=' u ']' t" := (subst_type x u t).

(** end of substitutions **) 


Definition subst_in_type := fun x r ty => subst_type x (Rgn2_Const true false r) ty.

Definition subst_in_eff := fun x r eff => subst_eps x (Rgn2_Const true false r) eff.

Definition subst_in_sa := fun x r sa => subst_sa x (Rgn2_Const true false r) sa.

Definition subst_in_rgn := fun x r rgn => subst_rgn x (Rgn2_Const true false r) rgn.

Definition subst_rho := R.fold subst_in_type.

Definition fold_subst_rgn := R.fold (fun x r rgn => subst_rgn x (Rgn2_Const true false r) rgn).

Definition fold_subst_sa rho sa:=
  match sa with
    | SA2_Alloc rgn => SA2_Alloc (fold_subst_rgn rho rgn)
    | SA2_Read rgn => SA2_Read (fold_subst_rgn rho rgn)
    | SA2_Write rgn => SA2_Write (fold_subst_rgn rho rgn)
  end.

Definition fold_subst_eps rho eps :=
  fun sa => exists sa', eps sa' /\ fold_subst_sa rho sa' = sa.



(*Notation "'∅'" := (Empty)  (at level 60).*)
(*Notation "'⊤'" := (Top) (at level 60).*)
Notation "a '⊕' b" := (Concat a b) (at level 60).

Reserved Notation "ctxt ';;' rgns ';;' rho '|-' ec '<<' ee" (at level 50, left associativity).
Inductive TcExp : (Gamma * Omega  * Expr * tau * Epsilon) -> Prop :=
  | TC_Nat_Cnt     : forall ctxt rgns n,
                        TcExp (ctxt, rgns, Const n, Ty2_Natural, Empty_Static_Action) 
  | TC_Boolean     : forall ctxt rgns b,
                        TcExp (ctxt, rgns, Bool b, Ty2_Boolean, Empty_Static_Action)
  | TC_Val_Var     : forall ctxt rgns x ty,
                        find_T x ctxt = Some ty ->
                        TcExp (ctxt, rgns, Var x, ty, Empty_Static_Action)
  | TC_Mu_Abs      : forall ctxt rgns f x ec ee tyx effc tyc effe,
                        (forall rho,
                          (BackTriangle 
                             (update_rec_T 
                                (f, Ty2_Arrow tyx effc tyc effe Ty2_Effect) (x, tyx) ctxt,
                              rgns, rho, ec, ee))) ->
                        (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
                        included (frv (Ty2_Arrow tyx effc tyc effe Ty2_Effect)) rgns ->
                        (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
                        TcExp (update_rec_T (f, Ty2_Arrow tyx effc tyc effe Ty2_Effect) 
                                            (x, tyx) ctxt, 
                               rgns, ec, tyc, effc) ->
                        TcExp (update_rec_T (f, Ty2_Arrow tyx effc tyc effe Ty2_Effect) 
                                            (x, tyx) ctxt, 
                               rgns, ee, Ty2_Effect, effe) ->
                        TcExp (ctxt, rgns, Mu f x ec ee, Ty2_Arrow tyx effc tyc effe Ty2_Effect,
                               Empty_Static_Action)
  | TC_Rgn_Abs     : forall ctxt rgns x er effr tyr,
                       not_set_elem rgns x ->
                       lc_type tyr ->
                       lc_type_eps effr ->
                       (forall rho, 
                          BackTriangle (ctxt, set_union rgns (singleton_set x), rho, er, Empty)) ->
                       TcExp (ctxt, set_union rgns (singleton_set x), er, tyr, effr) ->
                       TcExp (ctxt, rgns, Lambda x er, Ty2_ForallRgn 
                                                         (close_var_eff x effr) 
                                                         (close_var x tyr), 
                              Empty_Static_Action)
  | TC_Mu_App      : forall ctxt rgns ef ea tya effc tyc effe efff effa,
                       (forall rho, BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea)) ->
                       TcExp (ctxt, rgns, ef, Ty2_Arrow tya effc tyc effe Ty2_Effect, efff) ->
                       TcExp (ctxt, rgns, ea, tya, effa) ->
                       included (free_rgn_vars_in_eps effc) rgns ->
                       TcExp (ctxt, rgns, Mu_App ef ea, 
                              tyc, Union_Static_Action (Union_Static_Action efff effa) effc)
  | TC_Rgn_App     : forall ctxt rgns er w tyr effr efff,
                       TcExp (ctxt, rgns, er, Ty2_ForallRgn effr tyr, efff) ->
                       TcRgn (rgns, w) ->
                       (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
                       lc_type tyr ->
                       included (free_rgn_vars_in_eps (open_rgn_eff (mk_rgn_type w) effr)) rgns ->
                       (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
                       TcExp (ctxt, rgns,  Rgn_App er w, open (mk_rgn_type w) tyr,
                              Union_Static_Action efff (open_rgn_eff (mk_rgn_type w) effr))
  | TC_Eff_App     : forall ctxt rgns ef ea tya effc tyc effe efff effa,
                       TcExp (ctxt, rgns, ef, Ty2_Arrow tya effc tyc effe Ty2_Effect, efff) ->
                       TcExp (ctxt, rgns, ea, tya, effa) ->
                       included (free_rgn_vars_in_eps effe) rgns ->
                       TcExp (ctxt, rgns, Eff_App ef ea, 
                              Ty2_Effect, Union_Static_Action (Union_Static_Action efff effa) effe)
  | TC_Pair_Par    : forall ctxt rgns ef1 ea1 ef2 ea2 ty1 ty2 ty3 ty4 eff1 eff2 eff3 eff4,
                       TcExp (ctxt, rgns, Mu_App ef1 ea1, ty1, eff1) ->
                       TcExp (ctxt, rgns, Mu_App ef2 ea2, ty2, eff2) ->
                       TcExp (ctxt, rgns, Eff_App ef1 ea1, ty3, eff3) ->
                       TcExp (ctxt, rgns, Eff_App ef2 ea2, ty4, eff4) ->
                       TcExp (ctxt, rgns, Pair_Par ef1 ea1 ef2 ea2, Ty2_Pair ty1 ty2, 
                             Union_Static_Action 
                               (Union_Static_Action 
                                  (Union_Static_Action eff3 eff4) eff2) eff1)
  | TC_New_Ref     : forall ctxt rgns e t veff w s,      
                       TcExp (ctxt, rgns, e, t, veff) -> 
                       w = Rgn2_Const true false s ->
                       (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
                       included (free_rgn_vars_in_eps 
                                   (Singleton_Static_Action (SA_Alloc (mk_rgn_type w)))) rgns ->
                       (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
                       TcExp (ctxt, rgns, Ref w e, Ty2_Ref (mk_rgn_type w) t,
                              Union_Static_Action veff 
                                                  (Singleton_Static_Action 
                                                     (SA_Alloc (mk_rgn_type w))))
  | TC_Get_Ref     : forall ctxt rgns e t aeff w s,
                       w = Rgn2_Const true false s ->
                       TcExp (ctxt, rgns, e, Ty2_Ref (mk_rgn_type w) t, aeff) ->
                       TcRgn (rgns, w) ->
                       (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
                       included (free_rgn_vars_in_eps 
                                   (Singleton_Static_Action (SA_Read (mk_rgn_type w)))) rgns ->
                       (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
                       TcExp (ctxt, rgns, DeRef w e, t, 
                              Union_Static_Action aeff 
                                                  (Singleton_Static_Action 
                                                     (SA_Read  (mk_rgn_type w))))
  | TC_Set_Ref     : forall ctxt rgns ea ev t aeff veff w s,
                       w = Rgn2_Const true false s -> 
                       TcExp (ctxt, rgns, ea, Ty2_Ref (mk_rgn_type w) t, aeff) ->
                       TcExp (ctxt, rgns, ev, t, veff) ->
                       TcRgn (rgns, w) ->
                       (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
                       included (free_rgn_vars_in_eps
                                   (Singleton_Static_Action (SA_Write (mk_rgn_type w)))) rgns ->
                       (* +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
                       TcExp (ctxt, rgns, Assign w ea ev, Ty2_Unit,
                              Union_Static_Action (
                                  Union_Static_Action aeff veff) 
                                                  (Singleton_Static_Action 
                                                     (SA_Write  (mk_rgn_type w))))
  | TC_Conditional : forall ctxt rgns b e1 e2 te eff eff1 eff2,     
                       TcExp (ctxt, rgns, b, Ty2_Boolean, eff) ->         
                       TcExp (ctxt, rgns, e1, te, eff1) -> 
                       TcExp (ctxt, rgns, e2, te, eff2) -> 
                       TcExp (ctxt, rgns, Cond b e1 e2, te, 
                              Union_Static_Action eff 
                                                  (Union_Static_Action eff1 eff2))
  | TC_Nat_Plus    : forall ctxt rgns e1 e2 eff1 eff2,   
                       TcExp (ctxt, rgns, e1, Ty2_Natural, eff1) ->
                       TcExp (ctxt, rgns, e2, Ty2_Natural, eff2) -> 
                       TcExp (ctxt, rgns, Plus e1 e2, Ty2_Natural, Union_Static_Action eff1 eff2)
  | TC_Nat_Minus   : forall ctxt rgns e1 e2 eff1 eff2,   
                       TcExp (ctxt, rgns, e1, Ty2_Natural, eff1) ->
                       TcExp (ctxt, rgns, e2, Ty2_Natural, eff2) -> 
                       TcExp (ctxt, rgns, Minus e1 e2, Ty2_Natural, Union_Static_Action eff1 eff2)
  | TC_Nat_Times   : forall ctxt rgns e1 e2 eff1 eff2,   
                       TcExp (ctxt, rgns, e1, Ty2_Natural, eff1) ->
                       TcExp (ctxt, rgns, e2, Ty2_Natural, eff2) -> 
                       TcExp (ctxt, rgns, Times e1 e2, Ty2_Natural, Union_Static_Action eff1 eff2)
  | TC_Bool_Eq     : forall ctxt rgns e1 e2 eff1 eff2,   
                       TcExp (ctxt, rgns, e1, Ty2_Natural, eff1) ->
                       TcExp (ctxt, rgns, e2, Ty2_Natural, eff2) -> 
                       TcExp (ctxt, rgns, Eq e1 e2, Ty2_Boolean, Union_Static_Action eff1 eff2)
  | TC_Alloc_Abs   : forall ctxt rgns r,
                       TcExp (ctxt, rgns, AllocAbs r, Ty2_Effect, Empty_Static_Action)
  | TC_Read_Abs    : forall ctxt rgns r,
                       TcExp (ctxt, rgns, ReadAbs r, Ty2_Effect, Empty_Static_Action)
  | TC_Read_Conc   : forall ctxt rgns e r t aeff,
                       TcExp (ctxt, rgns, e, Ty2_Ref (Rgn2_Const true true r) t, aeff) ->
                       TcExp (ctxt, rgns, ReadConc e, Ty2_Effect, aeff)
  | TC_Write_Abs   : forall ctxt rgns r,
                       TcExp (ctxt, rgns,  WriteAbs r, Ty2_Effect, Empty_Static_Action)
  | TC_Write_Conc  : forall ctxt rgns e r t aeff,
                       TcExp (ctxt, rgns, e,  Ty2_Ref (Rgn2_Const true true r) t, aeff) ->
                       TcExp (ctxt, rgns, WriteConc e, Ty2_Effect, aeff)
  | TC_Eff_Concat  : forall ctxt rgns a b eff1 eff2,   
                       TcExp (ctxt, rgns, a, Ty2_Effect, eff1) ->
                       TcExp (ctxt, rgns, b, Ty2_Effect, eff2) -> 
                       TcExp (ctxt, rgns, Concat a b, Ty2_Effect, Union_Static_Action eff1 eff2)
  | TC_Eff_Top     : forall ctxt rgns,
                       TcExp (ctxt, rgns, Top, Ty2_Effect, Empty_Static_Action)
  | TC_Eff_Empty   : forall ctxt rgns,
                       TcExp (ctxt, rgns, Empty, Ty2_Effect, Empty_Static_Action)
   
with BackTriangle : Gamma * Omega * Rho * Expr * Expr -> Prop :=
  | BT_Num_Pure     : forall ctxt rgns rho (n : nat),
                        TcExp (ctxt, rgns, Const n, Ty2_Natural, Empty_Static_Action) ->
                        BackTriangle (ctxt, rgns, rho, (Const n), Empty)
  | BT_Bool_Pure    : forall ctxt rgns rho (b : bool),
                        TcExp (ctxt, rgns, Bool b, Ty2_Boolean, Empty_Static_Action) ->
                        BackTriangle (ctxt, rgns, rho, Bool b, Empty)
  | BT_Var_Pure     : forall ctxt rgns rho ty (x : VarId),
                        TcExp (ctxt, rgns, Var x, ty, Empty_Static_Action) ->
                        BackTriangle (ctxt, rgns, rho, Var x, Empty)
  | BT_Abs_Pure     : forall ctxt rgns rho (f x: VarId) (ec ee: Expr),
                        BackTriangle (ctxt, rgns, rho, Mu f x ec ee, Empty)
  | BT_Rgn_Pure     : forall ctxt rgns rho (x: VarId) (e: Expr),
                        BackTriangle (ctxt, rgns, rho, Lambda x e, Empty)
  | BT_App_Conc     : forall  ctxt rgns rho (ef ea: Expr)
                              ty_mu ty_eff ty_ef ty_ea  static_ef static_ea static_mu static_ee,
                        TcExp (ctxt, rgns, Mu_App ef ea, ty_mu, static_mu) ->
                        TcExp (ctxt, rgns, Eff_App ef ea, ty_eff, static_ee) ->
                        ReadOnlyStatic (fold_subst_eps rho static_ee) ->
                        TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
                        TcExp (ctxt, rgns, ea, ty_ea, static_ea) ->
                        BackTriangle (ctxt, rgns, rho, ef, Eff_App ef ea) ->
                        BackTriangle (ctxt, rgns, rho, ea, Eff_App ef ea) ->
                        ReadOnlyStatic (fold_subst_eps rho static_ef) ->
                        ReadOnlyStatic (fold_subst_eps rho static_ea) ->
                        BackTriangle (ctxt, rgns, rho, Mu_App ef ea, Eff_App ef ea)
  | BT_Pair_Par     : forall ctxt rgns rho ef1 ea1 ef2 ea2 eff1 eff2 eff3 eff4 
                             ty_e static_ee_1 static_ee_2,
                        TcExp (ctxt, rgns, Eff_App ef1 ea1, ty_e, static_ee_1) ->
                        ReadOnlyStatic (fold_subst_eps rho static_ee_1) ->
                        TcExp (ctxt, rgns, Eff_App ef2 ea2, ty_e, static_ee_2) ->
                        ReadOnlyStatic (fold_subst_eps rho static_ee_2) ->
                        BackTriangle (ctxt, rgns, rho, Eff_App ef1 ea1, eff1) ->
                        BackTriangle (ctxt, rgns, rho, Eff_App ef2 ea2, eff2) ->
                        BackTriangle (ctxt, rgns, rho, Mu_App ef1 ea1, eff3) ->
                        BackTriangle (ctxt, rgns, rho, Mu_App ef2 ea2, eff4) ->
                        BackTriangle (ctxt, rgns, rho, Pair_Par ef1 ea1 ef2 ea2,(eff1 ⊕ eff2) ⊕ (eff3 ⊕ eff4))
  | BT_Rgn_App      : forall ctxt rgns rho er w ty_eb static_er,
                        TcExp (ctxt, rgns, er, ty_eb, static_er) ->
                        TcExp (ctxt, rgns, Empty, Ty2_Effect, Empty_Static_Action) ->
                        BackTriangle (ctxt, rgns, rho, er, Empty) ->    
                        BackTriangle (ctxt, rgns, rho, Rgn_App er w, Empty)
  | BT_Cond_Cond    : forall ctxt rgns rho (e et ef effe efft efff : Expr) 
                             ty_e ty_et ty_ef static_e static_et static_ef,
                        TcExp (ctxt, rgns, e, ty_e, static_e) ->
                        TcExp (ctxt, rgns, et, ty_et, static_et) ->
                        TcExp (ctxt, rgns, ef, ty_ef, static_ef) ->
                        ReadOnlyStatic (fold_subst_eps rho static_e) ->
                        BackTriangle (ctxt, rgns, rho, e, Empty) ->
                        BackTriangle (ctxt, rgns, rho, et, efft) ->
                        BackTriangle (ctxt, rgns, rho, ef, efff) ->
                        BackTriangle (ctxt, rgns, rho, Cond e et ef, Cond e efft efff)
  | BT_Ref_Alloc_Abs : forall ctxt rgns rho (e eff : Expr) (w : Region_in_Expr) ty_e static_e,
                         TcExp (ctxt, rgns, e, ty_e, static_e) ->
                         BackTriangle (ctxt, rgns, rho, e, eff) ->
                         BackTriangle (ctxt, rgns, rho, Ref w e, eff ⊕ AllocAbs w)
  | BT_Ref_Read_Abs  : forall ctxt rgns rho (e eff : Expr) (w : Region_in_Expr) ty_e static_e,
                         TcExp (ctxt, rgns, e, ty_e, static_e) ->
                         BackTriangle (ctxt, rgns, rho, e, eff) ->
                         BackTriangle (ctxt, rgns, rho, DeRef w e, eff ⊕ (ReadAbs w))
  | BT_Ref_Read_Conc : forall ctxt rgns rho (e eff : Expr) (r : RgnId) ty_e static_e,
                         TcExp (ctxt, rgns, e, ty_e, static_e) ->
                         BackTriangle (ctxt, rgns, rho, e, Empty) ->
                         BackTriangle (ctxt, rgns, rho, DeRef (Rgn2_Const true false r) e, ReadConc e)
  | BT_Ref_Write_Abs : forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) (w : Region_in_Expr) 
                       ty_e1 static_e1,
                         BackTriangle (ctxt, rgns, rho, e1, eff1) ->
                         BackTriangle (ctxt, rgns, rho, e2, eff2) ->
                         TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
                         ReadOnlyStatic (fold_subst_eps rho static_e1) ->
                         BackTriangle (ctxt, rgns, rho, Assign w e1 e2, eff1 ⊕ (eff2 ⊕ (WriteAbs w)))
  | BT_Ref_Write_Conc: forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) (r : RgnId)
                       ty_e1 static_e1,
                         BackTriangle (ctxt, rgns, rho, e1, eff1) ->
                         BackTriangle (ctxt, rgns, rho, e2, eff2) ->
                         TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
                         ReadOnlyStatic (fold_subst_eps rho static_e1) ->
                         BackTriangle (ctxt, rgns, rho, 
                                       Assign (Rgn2_Const true false r) e1 e2, eff1 ⊕ (eff2 ⊕ (WriteConc e1)))
  | BT_Plus           : forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) 
                               ty_e1 ty_e2 static_e1 static_e2,
                        TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
                        TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
                        ReadOnlyStatic (fold_subst_eps rho static_e1) ->
                        BackTriangle (ctxt, rgns, rho, e1, eff1) ->
                        BackTriangle (ctxt, rgns, rho, e2, eff2) ->
                        BackTriangle (ctxt, rgns, rho, Plus e1 e2, eff1 ⊕ eff2)
  | BT_Minus          : forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) 
                               ty_e1 ty_e2 static_e1 static_e2,
                        TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
                        TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
                        ReadOnlyStatic (fold_subst_eps rho static_e1) ->
                        BackTriangle (ctxt, rgns, rho, e1, eff1) ->
                        BackTriangle (ctxt, rgns, rho, e2, eff2) ->
                        BackTriangle (ctxt, rgns, rho, Minus e1 e2, eff1 ⊕ eff2)
  | BT_Times          : forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) 
                               ty_e1 ty_e2 static_e1 static_e2,
                        TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
                        TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
                        ReadOnlyStatic (fold_subst_eps rho static_e1) ->
                        BackTriangle (ctxt, rgns, rho, e1, eff1) ->
                        BackTriangle (ctxt, rgns, rho, e2, eff2) ->
                        BackTriangle (ctxt, rgns, rho, Times e1 e2, eff1 ⊕ eff2)
 | BT_Eq           : forall ctxt rgns rho (e1 e2 eff1 eff2 : Expr) 
                            ty_e1 ty_e2 static_e1 static_e2,
                        TcExp (ctxt, rgns, e1, ty_e1, static_e1) ->
                        TcExp (ctxt, rgns, e2, ty_e2, static_e2) ->
                        ReadOnlyStatic (fold_subst_eps rho static_e1) ->
                        BackTriangle (ctxt, rgns, rho, e1, eff1) ->
                        BackTriangle (ctxt, rgns, rho, e2, eff2) ->
                        BackTriangle (ctxt, rgns, rho, Eq e1 e2, eff1 ⊕ eff2)
  | BT_Top_Approx    : forall ctxt rgns rho (e : Expr),
                         BackTriangle (ctxt, rgns, rho, e, Top)

with TcVal : (Sigma * Val * tau) -> Prop :=
  | TC_Num     : forall stty n,
                   TcVal (stty, Num n, Ty2_Natural)
  | TC_Bit     : forall stty b,
                   TcVal (stty, Bit b, Ty2_Boolean)
  | TC_Loc     : forall stty s l ty,
                   ST.find (s, l) stty = Some ty ->
                   (forall r, r # ty) ->
                   TcVal (stty, Loc (Rgn2_Const true false s) l, 
                          Ty2_Ref (Rgn2_Const true true s) ty)
  | TC_Cls     : forall stty env rho e rgns ctxt t,
                   TcRho (rho, rgns) ->
                   TcInc (ctxt, rgns) ->
                   TcEnv (stty, rho, env, ctxt) ->
                   TcExp (ctxt, rgns, e, t, Empty_Static_Action) ->
                   TcVal (stty, Cls (env, rho, e), subst_rho rho t) 
  | TC_Unit    : forall stty, 
                   TcVal (stty, Unit, Ty2_Unit)
  | TC_Pair    : forall stty v1 v2 ty1 ty2,
                   TcVal (stty, v1, ty1) ->
                   TcVal (stty, v2, ty2) ->
                   TcVal (stty, Pair (v1, v2), Ty2_Pair ty1 ty2)
  | TC_Eff     : forall stty e, 
                   TcVal (stty, Eff e, Ty2_Effect)
                        
with TcEnv : (Sigma * Rho * Env * Gamma) -> Prop :=
  | TC_Env : forall stty rho env ctxt, 
               E.Raw.bst env ->
               (forall x v, 
                  (find_E x env = Some v -> 
                   exists t, find_T x ctxt = Some t)) ->
               (forall x t,
                  (find_T x ctxt = Some t ->
                   exists v, find_E x env = Some v)) ->
               (forall x v t,
                  find_E x env = Some v -> 
                  find_T x ctxt = Some t ->
                  TcVal (stty, v, subst_rho rho t)) ->
               TcEnv (stty, rho, env, ctxt)

where "ctxt ';;' rgns ';;' rho '|-' ec '<<' ee" := (BackTriangle (ctxt, rgns, rho, ec, ee)) : type_scope.



Scheme tc_exp__xind := Induction for TcExp Sort Prop
  with bt__xind     := Induction for BackTriangle Sort Prop
  with tc_val__xind := Induction for TcVal Sort Prop
  with tc_env__xind := Induction for TcEnv Sort Prop.

Combined Scheme tc__xind from 
  tc_exp__xind, 
  bt__xind,
  tc_val__xind, 
  tc_env__xind.






 
