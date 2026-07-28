From stdpp Require Import gmap.
From stdpp Require Import strings.
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Ascii.
Require Import theories.BigStep.Core.Regions.
Require Import theories.BigStep.Core.ComputedActions.
Require Import theories.BigStep.Core.StaticActions.
Require Import theories.BigStep.Core.Values.
Require Import theories.BigStep.Core.Expressions.

Inductive Tau :=
  | Ty_Natural : Tau
  | Ty_Boolean : Tau
  | Ty_Effect  : Tau
  | Ty_Unit    : Tau
  | Ty_Pair    : Tau -> Tau -> Tau
  | Ty_Ref     : Region_in_Type -> Tau -> Tau
  | Ty_Arrow   : Tau -> Epsilon -> Tau -> Epsilon -> Tau -> Tau
  | Ty_ForallRgn : Epsilon -> Tau -> Tau.

Definition SigmaKey := prod nat nat.
Definition Sigma := gmap SigmaKey Tau.
Definition Gamma := gmap VarId Tau.
Definition Omega : Type := Ensemble VarId.


Definition keys_eq x y := Nat.eq (fst x) (fst y) /\ Nat.eq (snd x) (snd y).

Lemma keys_eq_dec : forall (k : nat * nat) (k' : nat * nat),
    { keys_eq k k' } + { ~ keys_eq k k' }.
Proof.
  intros. unfold keys_eq, Nat.eq. destruct k as (r, l);
    destruct k' as (r', l'); subst; simpl.
  destruct (eq_nat_dec r r'); destruct (eq_nat_dec l l'). 
  - left. unfold Nat.eq. auto.
  - right. intro. contradict n. intuition.
  - right. intro. contradict n. intuition.
  - right. intro. contradict n. intuition.
Qed.    


Definition find_ST (k: SigmaKey) (m: Sigma) : option Tau := m !! k.
Definition update_ST (k: SigmaKey) (t: Tau) (m: Sigma) :=  <[ k := t ]>  m.


Definition Merge_ST (v1 v2 : option Tau) : option Tau :=
  match (v1, v2) with
  | (None, None) => None
  | (None, Some v) => Some v
  | (Some v, None) => Some v                           
  | (Some v, _) => Some v
end.

Definition Functional_Map_Union_Sigma (stty1 stty2 : Sigma) : Sigma
  := merge Merge_ST stty1 stty2.


Definition find_T (k: VarId) (m: Gamma) : option Tau :=  m !! k.

Definition update_T (p: VarId * Tau) (m : Gamma) := <[ fst p := snd p ]>  m.

Definition update_rec_T (f: VarId * Tau) (x: VarId * Tau) m :=
  let m' := update_T f m
  in update_T x m'.


(** begin of free regions **)
Definition free_rgn_vars_in_rgn (rgn: Region_in_Type) : Ensemble RgnName :=
  match rgn with
  | Rgn_Const _ _ _ => empty_set
  | Rgn_FVar _ _ n => singleton_set n
  | Rgn_BVar _ _ _ => empty_set
  end.

Definition free_region (rgn: Region_in_Type) : Ensemble RgnName := free_rgn_vars_in_rgn rgn.


Definition free_rgn_vars_in_sa (sa: StaticAction) : Ensemble RgnName :=
  match sa with
  | SA_Alloc rgn => free_rgn_vars_in_rgn rgn
  | SA_Read rgn => free_rgn_vars_in_rgn rgn
  | SA_Write rgn => free_rgn_vars_in_rgn rgn
  end.


Definition free_rgn_vars_in_eps (eps: Epsilon) : Ensemble RgnName := 
  fun n => exists (sa : StaticAction),
             eps sa /\ (free_rgn_vars_in_sa sa) n.


Fixpoint frv (t: Tau) : Ensemble VarId :=
  match t with
  | Ty_Natural    => empty_set
  | Ty_Boolean    => empty_set
  | Ty_Effect     => empty_set
  | Ty_Unit       => empty_set
  | Ty_Pair t1 t2 => set_union (frv t1) (frv t2)                        
  | Ty_Ref rgn ty => set_union (free_rgn_vars_in_rgn rgn) (frv ty)
  | Ty_Arrow aty ceff crty eeff erty =>
      set_union (frv aty)
        (set_union (set_union (free_rgn_vars_in_eps ceff)
                      (free_rgn_vars_in_eps eeff))
           (set_union (frv crty)(frv erty)))
  | Ty_ForallRgn eff rty =>
      set_union (free_rgn_vars_in_eps eff) (frv rty)                                      
  end.

Fixpoint not_set_elem_frv (t: Tau) x : Prop :=
  match t with
    | Ty_Natural    => True
    | Ty_Boolean    => True 
    | Ty_Effect     => True
    | Ty_Unit       => True
    | Ty_Pair t1 t2 => (not_set_elem (frv t1) x) /\ (not_set_elem (frv t2) x)  
    | Ty_Ref rgn ty => (not_set_elem (free_rgn_vars_in_rgn rgn) x) /\ 
                       (not_set_elem (frv ty) x)
    | Ty_Arrow aty ceff crty eeff erty 
      => (not_set_elem (frv aty) x) /\
         (not_set_elem (free_rgn_vars_in_eps ceff) x) /\
         (not_set_elem (free_rgn_vars_in_eps eeff) x) /\
         (not_set_elem (frv crty) x) /\
         (not_set_elem (frv erty) x)
    | Ty_ForallRgn eff rty => (not_set_elem (free_rgn_vars_in_eps eff) x) /\
                              (not_set_elem (frv rty) x)
  end.


Notation "x '#' t" := (not_set_elem (frv t) x) (at level 60).


(** locally closed **)
Inductive lc_type_rgn : Region_in_Type -> Prop :=
     | lc_rgn_const : forall r, lc_type_rgn (Rgn_Const true true r)
     | lc_rgn_fvar  : forall r, lc_type_rgn (Rgn_FVar true true r).

Inductive lc_type_sa : StaticAction -> Prop :=
     | lc_sa_alloc : forall r, lc_type_rgn (r) -> lc_type_sa (SA_Alloc r)
     | lc_sa_read  : forall r, lc_type_rgn (r) -> lc_type_sa (SA_Read r)
     | lc_sa_write : forall r, lc_type_rgn (r) -> lc_type_sa (SA_Write r).

Inductive lc_type_eps : Epsilon -> Prop :=
     | lc_eps : forall eps, (forall (sa : StaticAction), eps sa /\ lc_type_sa (sa)) ->
                            lc_type_eps (eps).


Definition mk_rgn_type (u: Region_in_Expr) : Region_in_Type
 := match u with
      | Rgn_Const fv bv n => Rgn_Const true true n
      | Rgn_FVar c bv n => Rgn_FVar true true n
      | Rgn_BVar c fv n => Rgn_BVar true true n                              
    end.

Definition lc u := lc_type_rgn (mk_rgn_type u).


(** begin of openings **)
Definition opening_rgn_in_rgn (k : nat) (u: Region_in_Type) (t: Region_in_Type) : Region_in_Type
 := match t with
    | Rgn_Const _ _ _ => t
    | Rgn_FVar _ _ _ => t
    | Rgn_BVar _ _ n => if (Nat.eqb n k) then u else t
    end.

Definition opening_rgn_in_sa (k : nat) (u: Region_in_Type) (sa: StaticAction) : StaticAction :=
  match sa with
  | SA_Alloc rgn => SA_Alloc (opening_rgn_in_rgn k u rgn)
  | SA_Read rgn  => SA_Read (opening_rgn_in_rgn k u rgn)
  | SA_Write rgn => SA_Write (opening_rgn_in_rgn k u rgn)
  end.

Definition opening_rgn_in_eps (k : nat) (u: Region_in_Type) (eps: Epsilon) : Epsilon := 
  fun sa => exists sa', eps sa' /\ opening_rgn_in_sa k u sa' = sa.

Fixpoint opening_rgn_exp (k: nat) (u: Region_in_Type) (t: Tau) {struct t} : Tau :=
  match t with
  | Ty_Natural => t
  | Ty_Boolean => t
  | Ty_Effect  => t
  | Ty_Unit    => t                     
  | Ty_Pair ty1 ty2  =>  Ty_Pair (opening_rgn_exp k u ty1)  (opening_rgn_exp k u ty2) 
  | Ty_Ref rgn ty => Ty_Ref (opening_rgn_in_rgn k u rgn) (opening_rgn_exp k u ty)
  | Ty_Arrow aty ceff crty eeff erty =>
      Ty_Arrow (opening_rgn_exp k u aty) (opening_rgn_in_eps k u ceff)
        (opening_rgn_exp k u crty) (opening_rgn_in_eps k u eeff)
        (opening_rgn_exp k u erty)
  | Ty_ForallRgn eff rty =>
      Ty_ForallRgn (opening_rgn_in_eps (S k) u eff) (opening_rgn_exp (S k) u rty)
  end.


Definition open_rgn_eff (u: Region_in_Type)  (eps: Epsilon) : Epsilon := opening_rgn_in_eps 0 u eps.
Definition open (u: Region_in_Type)  (t: Tau) : Tau := opening_rgn_exp 0 u t.
Definition open_var (t : Tau) (x : VarId) : Tau :=
  let rgn_fvar := Rgn_FVar true true x
  in opening_rgn_exp 0 (rgn_fvar) t.


(** begin of closings **)
Definition closing_rgn_in_rgn (k : nat) (x: RgnName) (t: Region_in_Type) : Region_in_Type
 := match t with
    | Rgn_Const _ _ _ => t
    | Rgn_FVar _ _ n  => if ascii_dec n x then (Rgn_BVar true true k) else t
    | Rgn_BVar _ _ _  => t
    end.

Definition closing_rgn_in_sa (k : nat) (x: RgnName) (sa: StaticAction) : StaticAction :=
  match sa with
  | SA_Alloc rgn => SA_Alloc (closing_rgn_in_rgn k x rgn)
  | SA_Read rgn  => SA_Read (closing_rgn_in_rgn k x rgn)
  | SA_Write rgn => SA_Write (closing_rgn_in_rgn k x rgn)
  end.

Definition closing_rgn_in_eps(k : nat) (x: RgnName) (eps: Epsilon) : Epsilon :=
  fun sa => exists sa', eps sa' /\ closing_rgn_in_sa k x sa' = sa.

Fixpoint closing_rgn_exp (k: nat) (x: RgnName) (t: Tau) {struct t} : Tau :=
  match t with
  | Ty_Natural => t
  | Ty_Boolean => t
  | Ty_Effect  => t
  | Ty_Unit    => t
  | Ty_Pair t1 t2 => Ty_Pair  (closing_rgn_exp k x t1) (closing_rgn_exp k x t2)
  | Ty_Ref rgn ty => Ty_Ref (closing_rgn_in_rgn k x rgn) (closing_rgn_exp k x ty)
  | Ty_Arrow aty ceff crty eeff erty =>
      Ty_Arrow (closing_rgn_exp k x aty)
        (closing_rgn_in_eps k x ceff) (closing_rgn_exp k x crty)
        (closing_rgn_in_eps k x eeff) (closing_rgn_exp k x erty)
  | Ty_ForallRgn eff rty =>
      Ty_ForallRgn (closing_rgn_in_eps (S k) x eff) (closing_rgn_exp (S k) x rty)
  end.


Definition close_var (x : VarId) (t : Tau) := closing_rgn_exp 0 x t.
Definition close_var_eff (x : VarId) (eps : Epsilon) := closing_rgn_in_eps 0 x eps.
(** end of closings **)



Inductive lc_type : Tau -> Prop :=
  | lc_natural : lc_type Ty_Natural
  | lc_pair    : forall t1 t2,
                   lc_type t1 -> lc_type t2 -> lc_type (Ty_Pair t1 t2)
  | lc_ref     : forall r t,
                   lc_type_rgn r -> lc_type t -> lc_type (Ty_Ref r t)
  | lc_arrow   : forall aty ceff crty eeff erty,
                   lc_type aty -> lc_type_eps ceff -> lc_type crty ->
                   lc_type_eps eeff -> lc_type erty ->
                   lc_type (Ty_Arrow aty ceff crty eeff erty)
  | lc_forall  : forall L eff rty,
                   (forall x, not_set_elem L x -> lc_type (open_var rty x)) ->
                   lc_type_eps eff ->
                   lc_type rty ->
                   lc_type (Ty_ForallRgn eff rty).
(** end of locally closed **)



Inductive TcRho : (Rho * Omega) -> Prop :=
| TC_Rho : forall rho rgns,
    (forall r, rho !! r <> None <-> set_elem rgns r) ->
    TcRho (rho, rgns).

Inductive TcInc : (Gamma * Omega) -> Prop :=
| Tc_Inc : forall ctxt rgns,
    (forall x t,
        find_T x ctxt = Some t -> included (frv t) rgns) ->
    TcInc (ctxt, rgns). 

Inductive TcRgn : (Omega * Region_in_Expr) -> Prop :=
| TC_Rgn_Const :
  forall rgns s,
    TcRgn (rgns, Rgn_Const true false s)
| TC_Rgn_Var :
  forall rgns r,
    set_elem rgns r ->
    TcRgn (rgns, Rgn_FVar true false r).      

(** begin of substitutions **)


Definition subst_rgn  (z : RgnName) (u : Region_in_Expr) (t: Region_in_Type) : Region_in_Type :=
  match t with
    | Rgn_Const _ _ r => t
    | Rgn_FVar _ _ r  => if (ascii_dec z r) then mk_rgn_type u else t 
    | Rgn_BVar _ _ _  => t
  end.


Definition subst_sa (z : RgnName) (u : Region_in_Expr) (t: StaticAction) : StaticAction :=
 match t with
  | SA_Alloc rgn => SA_Alloc (subst_rgn z u rgn)
  | SA_Read rgn  => SA_Read  (subst_rgn z u rgn)
  | SA_Write rgn => SA_Write (subst_rgn z u rgn)
 end.

Definition subst_eps  (z : RgnName) (u : Region_in_Expr) (t: Epsilon) : Epsilon :=
   fun sa => exists sa', t sa' /\ subst_sa z u sa' = sa.


Reserved Notation "'[' x ':=' u ']' t" (at level 20).
Fixpoint subst_type (z : RgnName) (u : Region_in_Expr) (t : Tau) {struct t} : Tau :=
  match t with
  | Ty_Natural => Ty_Natural
  | Ty_Boolean => Ty_Boolean
  | Ty_Effect  => Ty_Effect
  | Ty_Unit    => Ty_Unit
  | Ty_Pair t1 t2  => Ty_Pair (subst_type z u t1) (subst_type z u t2)
  | Ty_Ref r t => Ty_Ref (subst_rgn z u r) (subst_type z u t)
  | Ty_Arrow aty ceff crty eeff erty =>
      Ty_Arrow (subst_type z u aty) (subst_eps z u ceff) (subst_type z u crty)
        (subst_eps z u eeff) (subst_type z u erty)
  | Ty_ForallRgn eff rty => Ty_ForallRgn (subst_eps z u eff) (subst_type z u rty)
  end
where "'[' x ':=' u ']' t" := (subst_type x u t).

(** end of substitutions **) 


Definition subst_in_type := fun x r ty => subst_type x (Rgn_Const true false r) ty.

Definition subst_in_eff := fun x r eff => subst_eps x (Rgn_Const true false r) eff.

Definition subst_in_sa := fun x r sa => subst_sa x (Rgn_Const true false r) sa.

Definition subst_in_rgn (r : RgnName) (v : RgnVal) (rgn : Region_in_Type)
  := subst_rgn r (Rgn_Const true false v) rgn.

Definition subst_rho (rho : Rho) (t : Tau)
  := map_fold (fun r v t => subst_in_type r v t) t rho.

Definition fold_subst_rgn  (rho : Rho) (rt : Region_in_Type)
  := map_fold (fun x r rgn => subst_rgn x (Rgn_Const true false r) rgn) rt rho.


Definition fold_subst_sa rho sa:=
  match sa with
    | SA_Alloc rgn => SA_Alloc (fold_subst_rgn rho rgn)
    | SA_Read rgn => SA_Read (fold_subst_rgn rho rgn)
    | SA_Write rgn => SA_Write (fold_subst_rgn rho rgn)
  end.

Definition fold_subst_eps rho eps :=
  fun sa => exists sa', eps sa' /\ fold_subst_sa rho sa' = sa.

